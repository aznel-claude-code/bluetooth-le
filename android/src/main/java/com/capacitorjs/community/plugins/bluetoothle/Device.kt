package com.capacitorjs.community.plugins.bluetoothle

import android.annotation.SuppressLint
import android.annotation.TargetApi
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothDevice
import android.bluetooth.BluetoothGatt
import android.bluetooth.BluetoothGattCallback
import android.bluetooth.BluetoothGattCharacteristic
import android.bluetooth.BluetoothGattDescriptor
import android.bluetooth.BluetoothGattService
import android.bluetooth.BluetoothProfile
import android.bluetooth.BluetoothStatusCodes
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.os.Build
import android.os.Handler
import android.os.HandlerThread
import android.os.Looper
import androidx.annotation.RequiresApi
import com.getcapacitor.Logger
import java.util.Collections
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue

class CallbackResponse(
    val success: Boolean,
    val value: String,
)

class TimeoutHandler(
    val key: String,
    val handler: Handler
)

/**
 * The GATT status codes a connection callback actually reports, named.
 *
 * Android hands these to onConnectionStateChange and they are the only
 * evidence of WHY a link failed or dropped — 133 (a local stack failure,
 * usually retryable), 8 (the link timed out: out of range, or a peripheral
 * that stopped answering) and 19 (the peripheral closed the connection
 * itself) point at three different culprits and three different remedies.
 * Anything not listed is reported by number alone.
 */
fun gattStatusName(status: Int): String {
    return when (status) {
        0 -> "GATT_SUCCESS"
        8 -> "GATT_CONN_TIMEOUT"
        19 -> "GATT_CONN_TERMINATE_PEER_USER"
        22 -> "GATT_CONN_TERMINATE_LOCAL_HOST"
        34 -> "GATT_CONN_LMP_TIMEOUT"
        62 -> "GATT_CONN_FAIL_ESTABLISH"
        133 -> "GATT_ERROR"
        257 -> "GATT_FAILURE"
        else -> "unnamed"
    }
}

fun <T> ConcurrentLinkedQueue<T>.popFirstMatch(predicate: (T) -> Boolean): T? {
    synchronized(this) {
        val iterator = this.iterator()
        while (iterator.hasNext()) {
            val nextItem = iterator.next()
            if (predicate(nextItem)) {
                iterator.remove()
                return nextItem
            }
        }
        return null
    }
}

@SuppressLint("MissingPermission")
class Device(
    private val context: Context,
    bluetoothAdapter: BluetoothAdapter,
    private val address: String,
    private val onDisconnect: (status: Int) -> Unit
) {
    companion object {
        private val TAG = Device::class.java.simpleName
        private const val STATE_DISCONNECTED = 0
        private const val STATE_CONNECTING = 1
        private const val STATE_CONNECTED = 2
        private const val CLIENT_CHARACTERISTIC_CONFIG = "00002902-0000-1000-8000-00805f9b34fb"
        private const val REQUEST_MTU = 512

        // How long onMtuChanged is waited for before the connect call reports
        // success without it. See onServicesDiscovered.
        private const val MTU_EXCHANGE_TIMEOUT = 2000L
    }

    private var connectionState = STATE_DISCONNECTED
    private var device: BluetoothDevice = bluetoothAdapter.getRemoteDevice(address)
    private var bluetoothGatt: BluetoothGatt? = null
    private var callbackMap = HashMap<String, ((CallbackResponse) -> Unit)>()
    private val timeoutQueue = ConcurrentLinkedQueue<TimeoutHandler>()
    private var bondStateReceiver: BroadcastReceiver? = null
    private val pendingBondKeys = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
    private var currentMtu = -1
    private var skipDescriptorDiscovery = false

    private lateinit var callbacksHandlerThread: HandlerThread
    private lateinit var callbacksHandler: Handler

    private fun initializeCallbacksHandlerThread() {
        synchronized(this) {
            callbacksHandlerThread = HandlerThread("Callbacks thread")
            callbacksHandlerThread.start()
            callbacksHandler = Handler(callbacksHandlerThread.looper)
        }
    }

    // The GATT callbacks are delivered on callbacksHandler wherever the SDK
    // level allows one, so the MTU fallback posts there too: it calls resolve,
    // which mutates callbackMap, and a second thread would race onMtuChanged
    // for the same entry.
    private fun mtuFallbackHandler(): Handler {
        return if (::callbacksHandler.isInitialized) callbacksHandler
        else Handler(Looper.getMainLooper())
    }

    private fun cleanupCallbacksHandlerThread() {
        synchronized(this) {
            if (::callbacksHandlerThread.isInitialized) {
                callbacksHandlerThread.quitSafely()
            }
        }
    }

    fun cleanup() {
        synchronized(this) {
            bondStateReceiver?.let { receiver ->
                try {
                    context.unregisterReceiver(receiver)
                } catch (e: IllegalArgumentException) {
                    Logger.debug(TAG, "Bond state receiver already unregistered")
                }
                bondStateReceiver = null
            }

            pendingBondKeys.clear()
            cleanupCallbacksHandlerThread()
        }
    }

    private val gattCallback: BluetoothGattCallback = object : BluetoothGattCallback() {
        override fun onConnectionStateChange(
            gatt: BluetoothGatt, status: Int, newState: Int
        ) {
            val statusText = "status $status (${gattStatusName(status)})"
            Logger.debug(TAG, "onConnectionStateChange: newState $newState, $statusText")
            if (newState == BluetoothProfile.STATE_CONNECTED) {
                connectionState = STATE_CONNECTED
                // service discovery is required to use services
                Logger.debug(TAG, "Connected to GATT server. Starting service discovery.")
                val result = bluetoothGatt?.discoverServices()
                if (result != true) {
                    reject("connect", "Starting service discovery failed.")
                }
            } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                connectionState = STATE_DISCONNECTED
                onDisconnect(status)
                bluetoothGatt?.close()
                bluetoothGatt = null
                Logger.debug(TAG, "Disconnected from GATT server: $statusText")
                cleanup()
                // A connect still in flight has just FAILED, and this callback
                // carries the platform's own reason for it. Rejecting here is
                // what makes that reason reachable at all: otherwise the call
                // stays pending until its connection timeout expires, so every
                // GATT-level connect failure — 133 from the local stack, 8
                // from a link that dropped, 19 from a peripheral that hung up
                // — reaches the caller as the same contentless "Connection
                // timeout.", one whole timeout late. A no-op on an ordinary
                // disconnect, where no connect is registered.
                reject("connect", "Connection failed with $statusText.")
                resolve("disconnect", "Disconnected with $statusText.")
            }
        }

        override fun onServicesDiscovered(gatt: BluetoothGatt?, status: Int) {
            super.onServicesDiscovered(gatt, status)
            if (status == BluetoothGatt.GATT_SUCCESS) {
                resolve("discoverServices", "Services discovered.")
                if (connectCallOngoing()) {
                    // Try requesting a larger MTU. Maximally supported MTU will be selected.
                    requestMtu(REQUEST_MTU)
                    // A larger MTU is an optimization, not a precondition for
                    // being connected, so the connect call must not be gated on
                    // it. The exchange never answers when another app already
                    // holds the ACL link — its MTU is negotiated for the link,
                    // and the request lands on a wait list that never drains —
                    // which reported an established link with discovered
                    // services as "Connection timeout." 30s later, and tore it
                    // down (2026-08-01, Garmin Connect holding the same
                    // sensor). Whichever of this and onMtuChanged runs first
                    // resolves; the loser is a no-op.
                    mtuFallbackHandler().postDelayed({
                        resolve("connect", "Connected.")
                    }, MTU_EXCHANGE_TIMEOUT)
                }
            } else {
                reject("discoverServices", "Service discovery failed.")
                reject("connect", "Service discovery failed.")
            }
        }

        override fun onMtuChanged(gatt: BluetoothGatt?, mtu: Int, status: Int) {
            super.onMtuChanged(gatt, mtu, status)
            if (status == BluetoothGatt.GATT_SUCCESS) {
                currentMtu = mtu
                Logger.debug(TAG, "MTU changed: $mtu")
            } else {
                Logger.debug(TAG, "MTU change failed: $mtu")
            }
            resolve("connect", "Connected.")
        }

        override fun onReadRemoteRssi(gatt: BluetoothGatt?, rssi: Int, status: Int) {
            super.onReadRemoteRssi(gatt, rssi, status)
            val key = "readRssi"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                resolve(key, rssi.toString())
            } else {
                reject(key, "Reading RSSI failed.")
            }
        }

        @TargetApi(Build.VERSION_CODES.S_V2)
        override fun onCharacteristicRead(
            gatt: BluetoothGatt, characteristic: BluetoothGattCharacteristic, status: Int
        ) {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                // handled by new callback below
                return
            }
            Logger.verbose(TAG, "Using deprecated onCharacteristicRead.")
            super.onCharacteristicRead(gatt, characteristic, status)
            val key = "read|${characteristic.service.uuid}|${characteristic.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                val data = characteristic.value
                if (data != null) {
                    val value = bytesToString(data)
                    resolve(key, value)
                } else {
                    reject(key, "No data received while reading characteristic.")
                }
            } else {
                reject(key, "Reading characteristic failed.")
            }
        }

        @RequiresApi(api = Build.VERSION_CODES.TIRAMISU)
        override fun onCharacteristicRead(
            gatt: BluetoothGatt,
            characteristic: BluetoothGattCharacteristic,
            data: ByteArray,
            status: Int
        ) {
            Logger.verbose(TAG, "Using onCharacteristicRead from API level 33.")
            super.onCharacteristicRead(gatt, characteristic, data, status)
            val key = "read|${characteristic.service.uuid}|${characteristic.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                val value = bytesToString(data)
                resolve(key, value)
            } else {
                reject(key, "Reading characteristic failed.")
            }
        }

        override fun onCharacteristicWrite(
            gatt: BluetoothGatt, characteristic: BluetoothGattCharacteristic, status: Int
        ) {
            super.onCharacteristicWrite(gatt, characteristic, status)
            val key = "write|${characteristic.service.uuid}|${characteristic.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                resolve(key, "Characteristic successfully written.")
            } else {
                reject(key, "Writing characteristic failed.")
            }

        }

        @TargetApi(Build.VERSION_CODES.S_V2)
        override fun onCharacteristicChanged(
            gatt: BluetoothGatt, characteristic: BluetoothGattCharacteristic
        ) {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                // handled by new callback below
                return
            }
            Logger.verbose(TAG, "Using deprecated onCharacteristicChanged.")
            super.onCharacteristicChanged(gatt, characteristic)
            val notifyKey = "notification|${characteristic.service.uuid}|${characteristic.uuid}"
            val data = characteristic.value
            if (data != null) {
                val value = bytesToString(data)
                callbackMap[notifyKey]?.invoke(CallbackResponse(true, value))
            }
        }

        @RequiresApi(api = Build.VERSION_CODES.TIRAMISU)
        override fun onCharacteristicChanged(
            gatt: BluetoothGatt, characteristic: BluetoothGattCharacteristic, data: ByteArray
        ) {
            Logger.verbose(TAG, "Using onCharacteristicChanged from API level 33.")
            super.onCharacteristicChanged(gatt, characteristic, data)
            val notifyKey = "notification|${characteristic.service.uuid}|${characteristic.uuid}"
            val value = bytesToString(data)
            callbackMap[notifyKey]?.invoke(CallbackResponse(true, value))
        }

        @TargetApi(Build.VERSION_CODES.S_V2)
        override fun onDescriptorRead(
            gatt: BluetoothGatt, descriptor: BluetoothGattDescriptor, status: Int
        ) {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                // handled by new callback below
                return
            }
            Logger.verbose(TAG, "Using deprecated onDescriptorRead.")
            super.onDescriptorRead(gatt, descriptor, status)
            val key =
                "readDescriptor|${descriptor.characteristic.service.uuid}|${descriptor.characteristic.uuid}|${descriptor.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                val data = descriptor.value
                if (data != null) {
                    val value = bytesToString(data)
                    resolve(key, value)
                } else {
                    reject(key, "No data received while reading descriptor.")
                }
            } else {
                reject(key, "Reading descriptor failed.")
            }
        }

        @RequiresApi(api = Build.VERSION_CODES.TIRAMISU)
        override fun onDescriptorRead(
            gatt: BluetoothGatt, descriptor: BluetoothGattDescriptor, status: Int, data: ByteArray
        ) {
            Logger.verbose(TAG, "Using onDescriptorRead from API level 33.")
            super.onDescriptorRead(gatt, descriptor, status, data)
            val key =
                "readDescriptor|${descriptor.characteristic.service.uuid}|${descriptor.characteristic.uuid}|${descriptor.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                val value = bytesToString(data)
                resolve(key, value)
            } else {
                reject(key, "Reading descriptor failed.")
            }
        }

        override fun onDescriptorWrite(
            gatt: BluetoothGatt, descriptor: BluetoothGattDescriptor, status: Int
        ) {
            super.onDescriptorWrite(gatt, descriptor, status)
            val key =
                "writeDescriptor|${descriptor.characteristic.service.uuid}|${descriptor.characteristic.uuid}|${descriptor.uuid}"
            if (status == BluetoothGatt.GATT_SUCCESS) {
                resolve(key, "Descriptor successfully written.")
            } else {
                reject(key, "Writing descriptor failed.")
            }
        }
    }

    fun getId(): String {
        return address
    }

    /**
     * Actions that will be executed (see gattCallback)
     * - connect to gatt server
     * - discover services
     * - request MTU
     */
    fun connect(
        timeout: Long,
        skipDescriptorDiscovery: Boolean,
        autoConnect: Boolean,
        callback: (CallbackResponse) -> Unit
    ) {
        val key = "connect"
        this.skipDescriptorDiscovery = skipDescriptorDiscovery
        callbackMap[key] = callback
        if (isConnected()) {
            resolve(key, "Already connected.")
            return
        }
        bluetoothGatt?.close()
        connectionState = STATE_CONNECTING
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            initializeCallbacksHandlerThread()
            bluetoothGatt = device.connectGatt(
                context,
                autoConnect,
                gattCallback,
                BluetoothDevice.TRANSPORT_LE,
                BluetoothDevice.PHY_OPTION_NO_PREFERRED,
                callbacksHandler
            )
        } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            bluetoothGatt = device.connectGatt(
                context, autoConnect, gattCallback, BluetoothDevice.TRANSPORT_LE
            )
        } else {
            bluetoothGatt = device.connectGatt(
                context, autoConnect, gattCallback
            )
        }
        setConnectionTimeout(key, "Connection timeout.", bluetoothGatt, timeout)
    }

    private fun connectCallOngoing(): Boolean {
        return callbackMap.containsKey("connect")
    }

    fun isConnected(): Boolean {
        return bluetoothGatt != null && connectionState == STATE_CONNECTED
    }

    private fun requestMtu(mtu: Int) {
        Logger.debug(TAG, "requestMtu $mtu")
        val result = bluetoothGatt?.requestMtu(mtu)
        if (result != true) {
            reject("connect", "Starting requestMtu failed.")
        }
    }

    fun getMtu(): Int {
        return currentMtu
    }

    fun requestConnectionPriority(connectionPriority: Int): Boolean {
        return bluetoothGatt?.requestConnectionPriority(connectionPriority) ?: false
    }

    fun createBond(timeout: Long, callback: (CallbackResponse) -> Unit) {
        val key = "createBond"
        callbackMap[key] = callback

        // Check if already bonded first to avoid race condition
        if (isBonded()) {
            resolve(key, "Creating bond succeeded.")
            return
        }

        try {
            ensureBondStateReceiverRegistered()
        } catch (e: Exception) {
            Logger.error(TAG, "Error while registering bondStateReceiver: ${e.localizedMessage}", e)
            reject(key, "Creating bond failed.")
            return
        }
        val result = device.createBond()
        if (!result) {
            reject(key, "Creating bond failed.")
            return
        }
        // Wait for bond state change
        setTimeout(key, "Bonding timeout.", timeout)
    }

    private fun ensureBondStateReceiverRegistered() {
        synchronized(this) {
            if (bondStateReceiver != null) return

            bondStateReceiver = object : BroadcastReceiver() {
                override fun onReceive(ctx: Context, intent: Intent) {
                    if (intent.action == BluetoothDevice.ACTION_BOND_STATE_CHANGED) {
                        val updatedDevice =
                            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                                intent.getParcelableExtra(
                                    BluetoothDevice.EXTRA_DEVICE,
                                    BluetoothDevice::class.java
                                )
                            } else {
                                intent.getParcelableExtra<BluetoothDevice>(BluetoothDevice.EXTRA_DEVICE)
                            }

                        // BroadcastReceiver receives bond state updates from all devices, need to filter by device
                        if (device.address == updatedDevice?.address) {
                            val prev = intent.getIntExtra(BluetoothDevice.EXTRA_PREVIOUS_BOND_STATE, -1)
                            val state = intent.getIntExtra(BluetoothDevice.EXTRA_BOND_STATE, -1)
                            Logger.debug(TAG, "Bond state transition $prev -> $state")

                            // Handle createBond callback
                            if (callbackMap.containsKey("createBond")) {
                                if (state == BluetoothDevice.BOND_BONDED) {
                                    resolve("createBond", "Creating bond succeeded.")
                                } else if (prev == BluetoothDevice.BOND_BONDING && state == BluetoothDevice.BOND_NONE) {
                                    reject("createBond", "Creating bond failed.")
                                } else if (state == -1) {
                                    reject("createBond", "Creating bond failed.")
                                }
                            }

                            // Handle setNotifications callbacks (only for operations waiting on bonding)
                            if (prev == BluetoothDevice.BOND_BONDING && state == BluetoothDevice.BOND_NONE) {
                                val keysToReject = pendingBondKeys.toList()
                                pendingBondKeys.clear()
                                keysToReject.forEach { key ->
                                    reject(key, "Pairing request was cancelled by the user.")
                                }
                            }
                        }
                    }
                }
            }
            try {
                val intentFilter = IntentFilter(BluetoothDevice.ACTION_BOND_STATE_CHANGED)
                context.registerReceiver(bondStateReceiver, intentFilter)
            } catch (e: Exception) {
                Logger.error(TAG, "Error registering bond state receiver: ${e.localizedMessage}", e)
                bondStateReceiver = null
                throw e
            }
        }
    }

    fun isBonded(): Boolean {
        return device.bondState == BluetoothDevice.BOND_BONDED
    }

    fun disconnect(
        timeout: Long, callback: (CallbackResponse) -> Unit
    ) {
        val key = "disconnect"
        callbackMap[key] = callback
        if (bluetoothGatt == null) {
            resolve(key, "Disconnected.")
            return
        }
        bluetoothGatt?.disconnect()
        // A disconnect that never answers must still CLOSE the client, which a
        // plain setTimeout does not do — it only rejects, leaving the
        // BluetoothGatt registered. Android allows a small, fixed number of GATT
        // client registrations per device; leaking one per failed disconnect
        // walks the app toward a state where nothing connects and scans return
        // nothing, which is what a killed-while-connected app reproduces on
        // every retry (2026-08-01: "Disconnection timeout." once per 20s, for
        // minutes). setConnectionTimeout closes and cleans up before rejecting.
        setConnectionTimeout(key, "Disconnection timeout.", bluetoothGatt, timeout)
    }

    fun getServices(): MutableList<BluetoothGattService> {
        return bluetoothGatt?.services ?: mutableListOf()
    }

    fun getSkipDescriptorDiscovery(): Boolean {
        return skipDescriptorDiscovery
    }

    fun discoverServices(
        timeout: Long, callback: (CallbackResponse) -> Unit
    ) {
        val key = "discoverServices"
        callbackMap[key] = callback
        refreshDeviceCache()
        val result = bluetoothGatt?.discoverServices()
        if (result != true) {
            reject(key, "Service discovery failed.")
            return
        }
        setTimeout(key, "Service discovery timeout.", timeout)
    }

    private fun refreshDeviceCache(): Boolean {
        var result = false

        try {
            if (bluetoothGatt != null) {
                val refresh = bluetoothGatt!!.javaClass.getMethod("refresh")
                result = (refresh.invoke(bluetoothGatt) as Boolean)
            }
        } catch (e: Exception) {
            Logger.error(TAG, "Error while refreshing device cache: ${e.localizedMessage}", e)
        }

        Logger.debug(TAG, "Device cache refresh $result")
        return result
    }

    fun readRssi(
        timeout: Long, callback: (CallbackResponse) -> Unit
    ) {
        val key = "readRssi"
        callbackMap[key] = callback
        val result = bluetoothGatt?.readRemoteRssi()
        if (result != true) {
            reject(key, "Reading RSSI failed.")
            return
        }
        setTimeout(key, "Reading RSSI timeout.", timeout)
    }

    fun read(
        serviceUUID: UUID,
        characteristicUUID: UUID,
        timeout: Long,
        callback: (CallbackResponse) -> Unit
    ) {
        val key = "read|$serviceUUID|$characteristicUUID"
        callbackMap[key] = callback
        val service = bluetoothGatt?.getService(serviceUUID)
        val characteristic = service?.getCharacteristic(characteristicUUID)
        if (characteristic == null) {
            reject(key, "Characteristic not found.")
            return
        }
        val result = bluetoothGatt?.readCharacteristic(characteristic)
        if (result != true) {
            reject(key, "Reading characteristic failed.")
            return
        }
        setTimeout(key, "Read timeout.", timeout)
    }

    fun write(
        serviceUUID: UUID,
        characteristicUUID: UUID,
        value: String,
        writeType: Int,
        timeout: Long,
        callback: (CallbackResponse) -> Unit
    ) {
        val key = "write|$serviceUUID|$characteristicUUID"
        callbackMap[key] = callback
        val service = bluetoothGatt?.getService(serviceUUID)
        val characteristic = service?.getCharacteristic(characteristicUUID)
        if (characteristic == null) {
            reject(key, "Characteristic not found.")
            return
        }
        val bytes = stringToBytes(value)

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            val statusCode = bluetoothGatt?.writeCharacteristic(characteristic, bytes, writeType)
            if (statusCode != BluetoothStatusCodes.SUCCESS) {
                reject(key, "Writing characteristic failed with status code $statusCode.")
                return
            }
        } else {
            characteristic.value = bytes
            characteristic.writeType = writeType
            val result = bluetoothGatt?.writeCharacteristic(characteristic)
            if (result != true) {
                reject(key, "Writing characteristic failed.")
                return
            }
        }
        setTimeout(key, "Write timeout.", timeout)
    }

    fun setNotifications(
        serviceUUID: UUID,
        characteristicUUID: UUID,
        enable: Boolean,
        notifyCallback: ((CallbackResponse) -> Unit)?,
        timeout: Long,
        callback: (CallbackResponse) -> Unit,
    ) {
        val key = "writeDescriptor|$serviceUUID|$characteristicUUID|$CLIENT_CHARACTERISTIC_CONFIG"
        val notifyKey = "notification|$serviceUUID|$characteristicUUID"
        callbackMap[key] = callback
        if (notifyCallback != null) {
            callbackMap[notifyKey] = notifyCallback
        }
        val service = bluetoothGatt?.getService(serviceUUID)
        val characteristic = service?.getCharacteristic(characteristicUUID)
        if (characteristic == null) {
            reject(key, "Characteristic not found.")
            return
        }

        val result = bluetoothGatt?.setCharacteristicNotification(characteristic, enable)
        if (result != true) {
            reject(key, "Setting notification failed.")
            return
        }

        val descriptor = characteristic.getDescriptor(UUID.fromString(CLIENT_CHARACTERISTIC_CONFIG))
        if (descriptor == null) {
            reject(key, "Setting notification failed.")
            return
        }

        val value = if (enable) {
            if ((characteristic.properties and BluetoothGattCharacteristic.PROPERTY_NOTIFY) != 0) {
                BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE
            } else if ((characteristic.properties and BluetoothGattCharacteristic.PROPERTY_INDICATE) != 0) {
                BluetoothGattDescriptor.ENABLE_INDICATION_VALUE
            } else {
                BluetoothGattDescriptor.DISABLE_NOTIFICATION_VALUE
            }
        } else {
            BluetoothGattDescriptor.DISABLE_NOTIFICATION_VALUE
        }

        // Track this operation as potentially needing bonding
        if (!isBonded()) {
            try {
                ensureBondStateReceiverRegistered()
                pendingBondKeys.add(key)
            } catch (e: Exception) {
                // Don't fail the notification attempt just because bonding
                // can't be tracked. The call will still timeout if bonding is
                // required for some reason
                Logger.warn(TAG, "Error while registering bondStateReceiver: ${e.localizedMessage}")
            }
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            val statusCode = bluetoothGatt?.writeDescriptor(descriptor, value)
            if (statusCode != BluetoothStatusCodes.SUCCESS) {
                reject(key, "Setting notification failed with status code $statusCode.")
                return
            }
        } else {
            descriptor.value = value
            val resultDesc = bluetoothGatt?.writeDescriptor(descriptor)
            if (resultDesc != true) {
                reject(key, "Setting notification failed.")
                return
            }

        }
        setTimeout(key, "Setting notification timeout.", timeout)
        // wait for onDescriptorWrite
    }

    fun readDescriptor(
        serviceUUID: UUID,
        characteristicUUID: UUID,
        descriptorUUID: UUID,
        timeout: Long,
        callback: (CallbackResponse) -> Unit
    ) {
        val key = "readDescriptor|$serviceUUID|$characteristicUUID|$descriptorUUID"
        callbackMap[key] = callback
        val service = bluetoothGatt?.getService(serviceUUID)
        val characteristic = service?.getCharacteristic(characteristicUUID)
        if (characteristic == null) {
            reject(key, "Characteristic not found.")
            return
        }
        val descriptor = characteristic.getDescriptor(descriptorUUID)
        if (descriptor == null) {
            reject(key, "Descriptor not found.")
            return
        }
        val result = bluetoothGatt?.readDescriptor(descriptor)
        if (result != true) {
            reject(key, "Reading descriptor failed.")
            return
        }
        setTimeout(key, "Read descriptor timeout.", timeout)
    }

    fun writeDescriptor(
        serviceUUID: UUID,
        characteristicUUID: UUID,
        descriptorUUID: UUID,
        value: String,
        timeout: Long,
        callback: (CallbackResponse) -> Unit
    ) {
        val key = "writeDescriptor|$serviceUUID|$characteristicUUID|$descriptorUUID"
        callbackMap[key] = callback
        val service = bluetoothGatt?.getService(serviceUUID)
        val characteristic = service?.getCharacteristic(characteristicUUID)
        if (characteristic == null) {
            reject(key, "Characteristic not found.")
            return
        }
        val descriptor = characteristic.getDescriptor(descriptorUUID)
        if (descriptor == null) {
            reject(key, "Descriptor not found.")
            return
        }
        val bytes = stringToBytes(value)

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            val statusCode = bluetoothGatt?.writeDescriptor(descriptor, bytes)
            if (statusCode != BluetoothStatusCodes.SUCCESS) {
                reject(key, "Writing descriptor failed with status code $statusCode.")
                return
            }
        } else {
            descriptor.value = bytes
            val result = bluetoothGatt?.writeDescriptor(descriptor)
            if (result != true) {
                reject(key, "Writing descriptor failed.")
                return
            }
        }
        setTimeout(key, "Write timeout.", timeout)
    }

    private fun resolve(key: String, value: String) {
        pendingBondKeys.remove(key)
        callbackMap.remove(key)?.let { callback ->
            Logger.debug(TAG, "resolve: $key $value")
            timeoutQueue.popFirstMatch { it.key == key }?.handler?.removeCallbacksAndMessages(null)
            callback?.invoke(CallbackResponse(true, value))
        }
    }

    private fun reject(key: String, value: String) {
        pendingBondKeys.remove(key)
        callbackMap.remove(key)?.let { callback ->
            Logger.debug(TAG, "reject: $key $value")
            timeoutQueue.popFirstMatch { it.key == key }?.handler?.removeCallbacksAndMessages(null)
            callback?.invoke(CallbackResponse(false, value))
        }
    }

    // Both timeout setters dequeue their own entry as it FIRES, before doing
    // anything else. Leaving it to resolve/reject is not enough: those only
    // reach the popFirstMatch when the key is still registered in callbackMap,
    // so a timer that fires after its call already settled leaves a dead entry
    // behind forever. The next resolve for that key then pops the DEAD entry
    // instead of the live timer it meant to cancel — and the live one stays
    // armed and fires later into a healthy connection, where
    // setConnectionTimeout's handler runs gatt.disconnect() and gatt.close()
    // with no callback left to tell anyone.
    private fun setTimeout(
        key: String, message: String, timeout: Long
    ) {
        val handler = Handler(Looper.getMainLooper())
        val timeoutHandler = TimeoutHandler(key, handler)
        timeoutQueue.add(timeoutHandler)
        handler.postDelayed({
            timeoutQueue.remove(timeoutHandler)
            reject(key, message)
        }, timeout)
    }

    private fun setConnectionTimeout(
        key: String,
        message: String,
        gatt: BluetoothGatt?,
        timeout: Long,
    ) {
        val handler = Handler(Looper.getMainLooper())
        val timeoutHandler = TimeoutHandler(key, handler)
        timeoutQueue.add(timeoutHandler)
        handler.postDelayed({
            timeoutQueue.remove(timeoutHandler)
            connectionState = STATE_DISCONNECTED
            gatt?.disconnect()
            gatt?.close()
            cleanup()
            reject(key, message)
        }, timeout)
    }
}

package com.example.myapp

import android.accessibilityservice.AccessibilityService
import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.ClipData
import android.content.ClipDescription
import android.content.ContentProvider
import android.content.ContentValues
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.ServiceInfo
import android.content.res.ColorStateList
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.database.Cursor
import android.database.MatrixCursor
import android.net.Uri
import android.net.wifi.WifiManager
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.provider.Settings
import android.view.Gravity
import android.view.KeyEvent
import android.view.View
import android.view.ViewGroup
import android.view.accessibility.AccessibilityEvent
import android.webkit.MimeTypeMap
import android.widget.BaseAdapter
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ListView
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileNotFoundException
import java.io.FileOutputStream
import java.io.IOException
import java.io.InputStream
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.ServerSocket
import java.net.Socket
import java.net.SocketAddress
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger

const val TCP_PORT = 45455
const val UDP_PORT = 45454
const val MAGIC = 0x4C434231
const val CLIP_AUTH = "com.example.myapp.clipfiles"

fun mimeForName(n: String): String {
    val dot = n.lastIndexOf('.')
    if (dot < 0 || dot >= n.length - 1) return "application/octet-stream"
    val m = MimeTypeMap.getSingleton().getMimeTypeFromExtension(n.substring(dot + 1).lowercase())
    return m ?: "application/octet-stream"
}

// ───────────────────────── data classes ─────────────────────────

class OutItem(
    val id: String,
    val isText: Boolean,
    val name: String,
    val uriStr: String,
    val text: String,
    val size: Long
)

class InItem(val isText: Boolean, val name: String, val path: String, val size: Long)

class Batch(val id: String, val from: String, val time: Long, val items: List<InItem>)

class Peer(val id: String, nameInit: String, ipInit: String) {
    @Volatile var name: String = nameInit
    @Volatile var ip: String = ipInit
    @Volatile var lastSeen: Long = System.currentTimeMillis()
    @Volatile var selected: Boolean = true
}

class Row(val kind: Int, val text: String, val ref: String)

class Src(val stream: InputStream, val size: Long, val tmp: File?) {
    fun close() {
        try {
            stream.close()
        } catch (e: Exception) {
        }
        if (tmp != null) {
            try {
                tmp.delete()
            } catch (e: Exception) {
            }
        }
    }
}

fun fmtSize(n: Long): String {
    if (n < 1024L) return n.toString() + " B"
    val kb = n / 1024.0
    if (kb < 1024.0) return String.format(Locale.US, "%.1f KB", kb)
    val mb = kb / 1024.0
    if (mb < 1024.0) return String.format(Locale.US, "%.1f MB", mb)
    return String.format(Locale.US, "%.2f GB", mb / 1024.0)
}

// ───────────────────────── core engine ─────────────────────────

class Core(val ctx: Context) {
    val handler = Handler(Looper.getMainLooper())
    val prefs: SharedPreferences = ctx.getSharedPreferences("lanclip", Context.MODE_PRIVATE)
    val pool: ExecutorService = Executors.newCachedThreadPool()
    val peers = ConcurrentHashMap<String, Peer>()
    val staged = ArrayList<OutItem>()
    val inbox = ArrayList<Batch>()
    val inboxDir: File = File(ctx.filesDir, "inbox")
    val myId: String = loadId()
    @Volatile var myName: String = prefs.getString("name", null) ?: (Build.MODEL ?: "Android")
    @Volatile var onChange: (() -> Unit)? = null
    @Volatile var statusListener: ((String) -> Unit)? = null
    @Volatile var lastStatus: String = "Starting..."
    @Volatile var running: Boolean = false
    private val statusScheduled = AtomicBoolean(false)
    private val counter = AtomicInteger(0)
    private var multicastLock: WifiManager.MulticastLock? = null
    private var wifiLock: WifiManager.WifiLock? = null

    init {
        inboxDir.mkdirs()
        loadState()
    }

    private fun loadId(): String {
        val s = prefs.getString("id", null)
        if (s != null) return s
        val n = UUID.randomUUID().toString()
        prefs.edit().putString("id", n).apply()
        return n
    }

    fun newId(): String = UUID.randomUUID().toString()

    fun folderUri(): String? = prefs.getString("folder", null)

    fun setFolder(s: String) {
        prefs.edit().putString("folder", s).apply()
    }

    fun setName(n: String) {
        myName = n
        prefs.edit().putString("name", n).apply()
        changed()
    }

    // ---- UI notifications (throttled, never blocks) ----

    fun status(msg: String) {
        lastStatus = msg
        if (statusScheduled.compareAndSet(false, true)) {
            handler.postDelayed({
                statusScheduled.set(false)
                statusListener?.invoke(lastStatus)
            }, 120)
        }
    }

    fun changed() {
        handler.post { onChange?.invoke() }
    }

    // ---- start networking ----

    fun start() {
        if (running) return
        running = true
        try {
            val wm = ctx.applicationContext.getSystemService(Context.WIFI_SERVICE) as WifiManager
            val ml = wm.createMulticastLock("lanclip")
            ml.setReferenceCounted(false)
            ml.acquire()
            multicastLock = ml
            val wl = wm.createWifiLock(WifiManager.WIFI_MODE_FULL_HIGH_PERF, "lanclip")
            wl.setReferenceCounted(false)
            wl.acquire()
            wifiLock = wl
        } catch (e: Exception) {
        }
        pool.execute { serverLoop() }
        pool.execute { udpListen() }
        pool.execute { announceLoop() }
        status("Ready. Open this app on other devices on the same Wi-Fi.")
    }

    // ---- discovery ----

    private fun broadcastAddresses(): List<InetAddress> {
        val list = ArrayList<InetAddress>()
        try {
            list.add(InetAddress.getByName("255.255.255.255"))
        } catch (e: Exception) {
        }
        try {
            val en = NetworkInterface.getNetworkInterfaces()
            while (en != null && en.hasMoreElements()) {
                val ni = en.nextElement()
                if (!ni.isUp || ni.isLoopback) continue
                for (ia in ni.interfaceAddresses) {
                    val b = ia.broadcast
                    if (b != null) list.add(b)
                }
            }
        } catch (e: Exception) {
        }
        return list
    }

    private fun announceLoop() {
        var sock: DatagramSocket? = null
        try {
            val s = DatagramSocket()
            s.broadcast = true
            sock = s
            while (running) {
                val msg = "LANCLIP1|" + myId + "|" + myName.replace("|", " ")
                val data = msg.toByteArray(Charsets.UTF_8)
                for (addr in broadcastAddresses()) {
                    try {
                        s.send(DatagramPacket(data, data.size, addr, UDP_PORT))
                    } catch (e: Exception) {
                    }
                }
                val now = System.currentTimeMillis()
                var removed = false
                for (p in peers.values) {
                    if (now - p.lastSeen > 9000L) {
                        peers.remove(p.id)
                        removed = true
                    }
                }
                if (removed) changed()
                try {
                    Thread.sleep(2000)
                } catch (e: InterruptedException) {
                }
            }
        } catch (e: Exception) {
            status("Discovery error: " + e.message)
        } finally {
            try {
                sock?.close()
            } catch (e: Exception) {
            }
        }
    }

    private fun udpListen() {
        while (running) {
            var ds: DatagramSocket? = null
            try {
                val s = DatagramSocket(null as SocketAddress?)
                ds = s
                s.reuseAddress = true
                s.broadcast = true
                s.bind(InetSocketAddress(UDP_PORT))
                val buf = ByteArray(512)
                while (running) {
                    val pk = DatagramPacket(buf, buf.size)
                    s.receive(pk)
                    val msg = String(pk.data, 0, pk.length, Charsets.UTF_8)
                    val parts = msg.split("|")
                    if (parts.size >= 3 && parts[0] == "LANCLIP1" && parts[1] != myId) {
                        val ip = pk.address.hostAddress
                        if (ip != null) onPeerSeen(parts[1], parts[2], ip)
                    }
                }
            } catch (e: Exception) {
                try {
                    Thread.sleep(2000)
                } catch (e2: InterruptedException) {
                }
            } finally {
                try {
                    ds?.close()
                } catch (e: Exception) {
                }
            }
        }
    }

    private fun onPeerSeen(id: String, name: String, ip: String) {
        val existing = peers[id]
        if (existing == null) {
            peers[id] = Peer(id, name, ip)
            status("Device found: " + name)
            changed()
        } else {
            existing.lastSeen = System.currentTimeMillis()
            if (existing.ip != ip || existing.name != name) {
                existing.ip = ip
                existing.name = name
                changed()
            }
        }
    }

    // ---- receiving ----

    private fun serverLoop() {
        while (running) {
            var ss: ServerSocket? = null
            try {
                val s = ServerSocket()
                ss = s
                s.reuseAddress = true
                s.bind(InetSocketAddress(TCP_PORT), 50)
                while (running) {
                    val c = s.accept()
                    pool.execute { handleIncoming(c) }
                }
            } catch (e: Exception) {
                status("Listen error: " + e.message)
                try {
                    Thread.sleep(2000)
                } catch (e2: InterruptedException) {
                }
            } finally {
                try {
                    ss?.close()
                } catch (e: Exception) {
                }
            }
        }
    }

    private fun handleIncoming(s: Socket) {
        var batchDir: File? = null
        try {
            s.soTimeout = 60000
            s.tcpNoDelay = true
            val input = DataInputStream(BufferedInputStream(s.getInputStream(), 65536))
            if (input.readInt() != MAGIC) return
            input.readUTF()
            val fromName = input.readUTF()
            val count = input.readInt()
            if (count < 0 || count > 10000) return
            val batchId = System.currentTimeMillis().toString() + "_" + counter.incrementAndGet().toString()
            val dir = File(inboxDir, batchId)
            dir.mkdirs()
            batchDir = dir
            val items = ArrayList<InItem>()
            val buf = ByteArray(65536)
            for (i in 0 until count) {
                val isText = input.readByte().toInt() == 1
                val name = input.readUTF()
                val size = input.readLong()
                val f = File(dir, i.toString() + ".dat")
                var remaining = size
                var lastPct = -1
                FileOutputStream(f).use { out ->
                    while (remaining > 0L) {
                        val want = minOf(buf.size.toLong(), remaining).toInt()
                        val n = input.read(buf, 0, want)
                        if (n < 0) throw IOException("connection closed")
                        out.write(buf, 0, n)
                        remaining -= n.toLong()
                        if (size > 0L) {
                            val pct = (((size - remaining) * 100L) / size).toInt()
                            if (pct != lastPct) {
                                lastPct = pct
                                status("Receiving from " + fromName + ": " + pct.toString() + "%")
                            }
                        }
                    }
                }
                items.add(InItem(isText, name, f.absolutePath, size))
            }
            val os = s.getOutputStream()
            os.write(1)
            os.flush()
            val batch = Batch(batchId, fromName, System.currentTimeMillis(), items)
            handler.post { addBatch(batch) }
        } catch (e: Exception) {
            status("Receive failed: " + e.message)
            try {
                batchDir?.deleteRecursively()
            } catch (e2: Exception) {
            }
        } finally {
            try {
                s.close()
            } catch (e: Exception) {
            }
        }
    }

    private fun addBatch(b: Batch) {
        inbox.add(0, b)
        while (inbox.size > 10) {
            val old = inbox.removeAt(inbox.size - 1)
            try {
                File(inboxDir, old.id).deleteRecursively()
            } catch (e: Exception) {
            }
        }
        saveInbox()
        var files = 0
        var texts = 0
        for (it2 in b.items) {
            if (it2.isText) texts++ else files++
        }
        putBatchOnClipboard(b)
        status("Received from " + b.from + ": " + files.toString() + " file(s), " + texts.toString() + " text(s). Now long-press in any app and tap Paste.")
        changed()
    }

    private fun applyTextToClipboard(b: Batch) {
        try {
            val parts = ArrayList<String>()
            for (it2 in b.items) {
                if (it2.isText && it2.size <= 500000L) {
                    val f = File(it2.path)
                    if (f.exists()) parts.add(String(f.readBytes(), Charsets.UTF_8))
                }
            }
            if (parts.isNotEmpty()) setClipboardText(parts.joinToString("\n"))
        } catch (e: Exception) {
        }
    }

    fun setClipboardText(t: String) {
        try {
            val cm = ctx.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(ClipData.newPlainText("LAN Clipboard", t))
        } catch (e: Exception) {
        }
    }

    fun findBatch(id: String): Batch? {
        for (x in inbox) {
            if (x.id == id) return x
        }
        return null
    }

    fun putBatchOnClipboard(b: Batch): Boolean {
        try {
            var clip: ClipData? = null
            for ((idx, item) in b.items.withIndex()) {
                val ci: ClipData.Item
                val mime: String
                if (item.isText) {
                    val f = File(item.path)
                    if (!f.exists() || f.length() > 500000L) continue
                    ci = ClipData.Item(String(f.readBytes(), Charsets.UTF_8))
                    mime = "text/plain"
                } else {
                    var nm = item.name
                    if (nm.isEmpty()) nm = "file"
                    val uri = Uri.Builder()
                        .scheme("content")
                        .authority(CLIP_AUTH)
                        .appendPath(b.id)
                        .appendPath(idx.toString())
                        .appendPath(nm)
                        .build()
                    ci = ClipData.Item(uri)
                    mime = mimeForName(nm)
                }
                val cur = clip
                if (cur == null) {
                    clip = ClipData(ClipDescription("LAN Clipboard", arrayOf(mime)), ci)
                } else {
                    cur.addItem(ctx.contentResolver, ci)
                }
            }
            val fin = clip ?: return false
            val cm = ctx.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(fin)
            return true
        } catch (e: Exception) {
            return false
        }
    }

    // Reads the clipboard (works only when this app has focus) and sends it.
    // Returns 1 = sent, 2 = already sent / our own clip, 0 = nothing readable.
    fun sendCurrentClipboard(c: Context): Int {
        try {
            val cm = c.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            val clip = cm.primaryClip ?: return 0
            if (clip.itemCount == 0) return 0
            val lbl = clip.description.label
            if (lbl != null && lbl.toString() == "LAN Clipboard") return 2
            val uris = ArrayList<Uri>()
            val texts = ArrayList<String>()
            val sb = StringBuilder()
            for (k in 0 until clip.itemCount) {
                val item = clip.getItemAt(k)
                val u = item.uri
                if (u != null && u.scheme == "content") {
                    uris.add(u)
                    sb.append(u.toString()).append('|')
                } else {
                    val t = item.coerceToText(c)
                    if (t != null && t.isNotEmpty()) {
                        texts.add(t.toString())
                        sb.append(t.toString()).append('|')
                    }
                }
            }
            if (uris.isEmpty() && texts.isEmpty()) return 0
            val sig = sb.length.toString() + ":" + sb.toString().hashCode().toString()
            if (sig == prefs.getString("lastsig", "")) return 2
            prefs.edit().putString("lastsig", sig).apply()
            copyFiles(uris, texts)
            return 1
        } catch (e: Exception) {
            return 0
        }
    }

    // ---- copying (staging + sending) ----

    fun copyFiles(uris: List<Uri>, texts: List<String>) {
        pool.execute {
            val list = ArrayList<OutItem>()
            for (u in uris) {
                var name = "file"
                var size = -1L
                try {
                    val cur = ctx.contentResolver.query(u, null, null, null, null)
                    if (cur != null) {
                        cur.use { c ->
                            if (c.moveToFirst()) {
                                val ni = c.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                                if (ni >= 0 && !c.isNull(ni)) name = c.getString(ni)
                                val si = c.getColumnIndex(OpenableColumns.SIZE)
                                if (si >= 0 && !c.isNull(si)) size = c.getLong(si)
                            }
                        }
                    }
                } catch (e: Exception) {
                }
                if (!name.contains('.')) {
                    var ext: String? = null
                    try {
                        val t = ctx.contentResolver.getType(u)
                        if (t != null) ext = MimeTypeMap.getSingleton().getExtensionFromMimeType(t)
                    } catch (e: Exception) {
                    }
                    if (ext != null) name = name + "." + ext
                }
                list.add(OutItem(newId(), false, name, u.toString(), "", size))
            }
            for (t in texts) {
                list.add(OutItem(newId(), true, "text", "", t, t.toByteArray(Charsets.UTF_8).size.toLong()))
            }
            handler.post { stageAndSend(list) }
        }
    }

    private fun stageAndSend(list: List<OutItem>) {
        if (list.isEmpty()) return
        staged.clear()
        staged.addAll(list)
        saveStaged()
        changed()
        resend()
    }

    fun resend() {
        if (staged.isEmpty()) {
            status("Nothing copied yet.")
            return
        }
        val targets = ArrayList<Peer>()
        for (p in peers.values) {
            if (p.selected) targets.add(p)
        }
        if (targets.isEmpty()) {
            status("Copied. No devices selected/found yet - press Resend when they appear.")
            return
        }
        val items = ArrayList<OutItem>(staged)
        for (p in targets) {
            pool.execute { sendTo(p, items) }
        }
    }

    private fun openSource(item: OutItem): Src {
        val uri = Uri.parse(item.uriStr)
        if (item.size >= 0L) {
            val st = ctx.contentResolver.openInputStream(uri) ?: throw IOException("cannot open " + item.name)
            return Src(st, item.size, null)
        }
        val tmp = File(ctx.cacheDir, "tmp_" + System.nanoTime().toString())
        val ins = ctx.contentResolver.openInputStream(uri) ?: throw IOException("cannot open " + item.name)
        val buf = ByteArray(65536)
        ins.use { i ->
            FileOutputStream(tmp).use { o ->
                while (true) {
                    val n = i.read(buf)
                    if (n < 0) break
                    o.write(buf, 0, n)
                }
            }
        }
        return Src(FileInputStream(tmp), tmp.length(), tmp)
    }

    private fun sendTo(p: Peer, items: List<OutItem>) {
        val s = Socket()
        try {
            s.tcpNoDelay = true
            s.connect(InetSocketAddress(p.ip, TCP_PORT), 4000)
            s.soTimeout = 60000
            val out = DataOutputStream(BufferedOutputStream(s.getOutputStream(), 65536))
            out.writeInt(MAGIC)
            out.writeUTF(myId)
            out.writeUTF(myName)
            out.writeInt(items.size)
            var total = 0L
            for (item in items) {
                total += if (item.isText) item.text.toByteArray(Charsets.UTF_8).size.toLong() else maxOf(item.size, 0L)
            }
            var sent = 0L
            var lastPct = -1
            val buf = ByteArray(65536)
            for (item in items) {
                if (item.isText) {
                    val bytes = item.text.toByteArray(Charsets.UTF_8)
                    out.writeByte(1)
                    out.writeUTF("")
                    out.writeLong(bytes.size.toLong())
                    out.write(bytes)
                    sent += bytes.size.toLong()
                } else {
                    val src = openSource(item)
                    try {
                        out.writeByte(0)
                        out.writeUTF(item.name)
                        out.writeLong(src.size)
                        var left = src.size
                        while (left > 0L) {
                            val want = minOf(buf.size.toLong(), left).toInt()
                            val n = src.stream.read(buf, 0, want)
                            if (n < 0) throw IOException("source ended early")
                            out.write(buf, 0, n)
                            left -= n.toLong()
                            sent += n.toLong()
                            val pct = if (total > 0L) ((sent * 100L) / total).toInt() else 100
                            if (pct != lastPct) {
                                lastPct = pct
                                status("Sending to " + p.name + ": " + pct.toString() + "%")
                            }
                        }
                    } finally {
                        src.close()
                    }
                }
            }
            out.flush()
            val ack = s.getInputStream().read()
            if (ack < 0) throw IOException("no confirmation")
            status("Sent " + items.size.toString() + " item(s) to " + p.name + " - done")
        } catch (e: Exception) {
            status("Failed to send to " + p.name + ": " + e.message)
        } finally {
            try {
                s.close()
            } catch (e: Exception) {
            }
        }
    }

    fun removeStaged(id: String) {
        var idx = -1
        for (k in 0 until staged.size) {
            if (staged[k].id == id) idx = k
        }
        if (idx >= 0) {
            staged.removeAt(idx)
            saveStaged()
            changed()
        }
    }

    fun clearAll() {
        staged.clear()
        for (b in inbox) {
            try {
                File(inboxDir, b.id).deleteRecursively()
            } catch (e: Exception) {
            }
        }
        inbox.clear()
        saveStaged()
        saveInbox()
        changed()
        status("Cleared.")
    }

    // ---- pasting ----

    private fun maxNumber(tree: Uri): Long {
        var best = 0L
        try {
            val children = DocumentsContract.buildChildDocumentsUriUsingTree(tree, DocumentsContract.getTreeDocumentId(tree))
            val cur = ctx.contentResolver.query(children, arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)
            if (cur != null) {
                cur.use { c ->
                    while (c.moveToNext()) {
                        val nm = c.getString(0)
                        if (nm != null) {
                            val dot = nm.lastIndexOf('.')
                            val base = if (dot > 0) nm.substring(0, dot) else nm
                            val v = base.toLongOrNull()
                            if (v != null && v > best) best = v
                        }
                    }
                }
            }
        } catch (e: Exception) {
        }
        return best
    }

    fun pasteBatch(b: Batch, tree: Uri?) {
        pool.execute {
            try {
                val texts = ArrayList<String>()
                var savedCount = 0
                var next = if (tree != null) maxNumber(tree) + 1L else 1L
                val parent: Uri? = if (tree != null) DocumentsContract.buildDocumentUriUsingTree(tree, DocumentsContract.getTreeDocumentId(tree)) else null
                val buf = ByteArray(65536)
                var totalFiles = 0
                for (it2 in b.items) {
                    if (!it2.isText) totalFiles++
                }
                for (item in b.items) {
                    if (item.isText) {
                        val f = File(item.path)
                        if (f.exists() && f.length() <= 2000000L) texts.add(String(f.readBytes(), Charsets.UTF_8))
                    } else {
                        if (parent == null) continue
                        val dot = item.name.lastIndexOf('.')
                        val ext = if (dot >= 0 && dot < item.name.length - 1) item.name.substring(dot + 1) else ""
                        var mime: String? = null
                        if (ext.isNotEmpty()) mime = MimeTypeMap.getSingleton().getMimeTypeFromExtension(ext.lowercase())
                        val mimeFinal: String = mime ?: "application/octet-stream"
                        val display = if (ext.isNotEmpty()) next.toString() + "." + ext else next.toString()
                        val doc = DocumentsContract.createDocument(ctx.contentResolver, parent, mimeFinal, display)
                            ?: throw IOException("Cannot create file in folder")
                        val os = ctx.contentResolver.openOutputStream(doc) ?: throw IOException("Cannot write file")
                        FileInputStream(File(item.path)).use { ins ->
                            os.use { o ->
                                while (true) {
                                    val n = ins.read(buf)
                                    if (n < 0) break
                                    o.write(buf, 0, n)
                                }
                            }
                        }
                        next++
                        savedCount++
                        status("Pasting " + savedCount.toString() + "/" + totalFiles.toString() + " ...")
                    }
                }
                val joined = texts.joinToString("\n")
                val msg = "Pasted " + savedCount.toString() + " file(s)" + (if (texts.isNotEmpty()) " + text (now in your clipboard)" else "") + "."
                handler.post {
                    if (joined.isNotEmpty()) setClipboardText(joined)
                }
                status(msg)
            } catch (e: Exception) {
                status("Paste failed: " + e.message)
            }
        }
    }

    // ---- persistence ----

    fun saveStaged() {
        try {
            val arr = JSONArray()
            for (s in staged) {
                val o = JSONObject()
                o.put("id", s.id)
                o.put("t", s.isText)
                o.put("n", s.name)
                o.put("u", s.uriStr)
                o.put("x", s.text)
                o.put("s", s.size)
                arr.put(o)
            }
            prefs.edit().putString("staged", arr.toString()).apply()
        } catch (e: Exception) {
        }
    }

    fun saveInbox() {
        try {
            val arr = JSONArray()
            for (b in inbox) {
                val o = JSONObject()
                o.put("id", b.id)
                o.put("from", b.from)
                o.put("time", b.time)
                val ia = JSONArray()
                for (i in b.items) {
                    val io = JSONObject()
                    io.put("t", i.isText)
                    io.put("n", i.name)
                    io.put("p", i.path)
                    io.put("s", i.size)
                    ia.put(io)
                }
                o.put("items", ia)
                arr.put(o)
            }
            prefs.edit().putString("inbox", arr.toString()).apply()
        } catch (e: Exception) {
        }
    }

    fun saveAll() {
        saveStaged()
        saveInbox()
    }

    private fun loadState() {
        try {
            val s = prefs.getString("staged", null)
            if (s != null) {
                val a = JSONArray(s)
                for (k in 0 until a.length()) {
                    val o = a.getJSONObject(k)
                    staged.add(
                        OutItem(
                            o.getString("id"), o.getBoolean("t"), o.getString("n"),
                            o.getString("u"), o.getString("x"), o.getLong("s")
                        )
                    )
                }
            }
        } catch (e: Exception) {
        }
        try {
            val s = prefs.getString("inbox", null)
            if (s != null) {
                val a = JSONArray(s)
                for (k in 0 until a.length()) {
                    val o = a.getJSONObject(k)
                    val ia = o.getJSONArray("items")
                    val items = ArrayList<InItem>()
                    var ok = true
                    for (m in 0 until ia.length()) {
                        val io = ia.getJSONObject(m)
                        val path = io.getString("p")
                        if (!File(path).exists()) ok = false
                        items.add(InItem(io.getBoolean("t"), io.getString("n"), path, io.getLong("s")))
                    }
                    if (ok && items.isNotEmpty()) {
                        inbox.add(Batch(o.getString("id"), o.getString("from"), o.getLong("time"), items))
                    }
                }
            }
        } catch (e: Exception) {
        }
    }
}

// ───────────────────────── file provider (lets other apps paste received files) ─────────────────────────

class ClipProvider : ContentProvider() {
    override fun onCreate(): Boolean = true

    private fun fileFor(uri: Uri): File? {
        val c = context ?: return null
        val segs = uri.pathSegments
        if (segs.size < 3) return null
        val batch = segs[0]
        val idx = segs[1]
        if (!batch.matches(Regex("[0-9_]+"))) return null
        if (!idx.matches(Regex("[0-9]+"))) return null
        val f = File(File(File(c.filesDir, "inbox"), batch), idx + ".dat")
        return if (f.exists()) f else null
    }

    override fun query(
        uri: Uri,
        projection: Array<out String>?,
        selection: String?,
        selectionArgs: Array<out String>?,
        sortOrder: String?
    ): Cursor? {
        val f = fileFor(uri) ?: return null
        val name = uri.lastPathSegment ?: "file"
        val cols: Array<String> = if (projection != null) {
            Array(projection.size) { k -> projection[k] }
        } else {
            arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE)
        }
        val cur = MatrixCursor(cols)
        val row = arrayOfNulls<Any>(cols.size)
        for (k in cols.indices) {
            if (cols[k] == OpenableColumns.DISPLAY_NAME) row[k] = name
            else if (cols[k] == OpenableColumns.SIZE) row[k] = f.length()
        }
        cur.addRow(row)
        return cur
    }

    override fun getType(uri: Uri): String? {
        val name = uri.lastPathSegment ?: return "application/octet-stream"
        return mimeForName(name)
    }

    override fun openFile(uri: Uri, mode: String): ParcelFileDescriptor? {
        val f = fileFor(uri) ?: throw FileNotFoundException("not found")
        return ParcelFileDescriptor.open(f, ParcelFileDescriptor.MODE_READ_ONLY)
    }

    override fun insert(uri: Uri, values: ContentValues?): Uri? = null

    override fun delete(uri: Uri, selection: String?, selectionArgs: Array<out String>?): Int = 0

    override fun update(uri: Uri, values: ContentValues?, selection: String?, selectionArgs: Array<out String>?): Int = 0
}

// ───────────────────────── auto-detect copy (accessibility) ─────────────────────────

// Invisible screen that appears for a split second so Android lets us read the clipboard.
class ClipGrabActivity : Activity() {
    private var done = false

    override fun onWindowFocusChanged(hasFocus: Boolean) {
        super.onWindowFocusChanged(hasFocus)
        if (hasFocus && !done) {
            done = true
            try {
                val core = CoreHolder.get(applicationContext)
                core.start()
                core.sendCurrentClipboard(this)
            } catch (e: Exception) {
            }
            finish()
        }
    }
}

class ClipAccessService : AccessibilityService() {
    private val handler = Handler(Looper.getMainLooper())
    private var lastTrigger = 0L
    private val copyWord = Regex("\\b(copy|cut)\\b")

    override fun onServiceConnected() {
        super.onServiceConnected()
        try {
            CoreHolder.get(applicationContext).start()
        } catch (e: Exception) {
        }
    }

    override fun onAccessibilityEvent(event: AccessibilityEvent?) {
        if (event == null) return
        if (event.eventType != AccessibilityEvent.TYPE_VIEW_CLICKED) return
        if (!looksLikeCopy(event)) return
        trigger()
    }

    // Ctrl+C / Ctrl+X (or Meta+C / Meta+X) on an external keyboard
    override fun onKeyEvent(event: KeyEvent?): Boolean {
        if (event != null && event.action == KeyEvent.ACTION_DOWN && event.repeatCount == 0 &&
            (event.isCtrlPressed || event.isMetaPressed) &&
            (event.keyCode == KeyEvent.KEYCODE_C || event.keyCode == KeyEvent.KEYCODE_X)
        ) {
            trigger()
        }
        return false
    }

    private fun trigger() {
        val now = System.currentTimeMillis()
        if (now - lastTrigger < 800L) return
        lastTrigger = now
        handler.postDelayed({ grab() }, 350)
    }

    override fun onInterrupt() {
    }

    private fun looksLikeCopy(e: AccessibilityEvent): Boolean {
        val sb = StringBuilder()
        val cd = e.contentDescription
        if (cd != null) sb.append(cd.toString()).append(' ')
        for (t in e.text) {
            if (t != null) sb.append(t.toString()).append(' ')
        }
        return copyWord.containsMatchIn(sb.toString().lowercase())
    }

    private fun grab() {
        var r = 0
        try {
            r = CoreHolder.get(applicationContext).sendCurrentClipboard(this)
        } catch (e: Exception) {
        }
        if (r == 0) {
            try {
                val i = Intent(this, ClipGrabActivity::class.java)
                i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_NO_ANIMATION)
                startActivity(i)
            } catch (e: Exception) {
            }
        }
    }
}

object CoreHolder {
    @Volatile var core: Core? = null

    @Synchronized
    fun get(ctx: Context): Core {
        val c = core
        if (c != null) return c
        val n = Core(ctx.applicationContext)
        core = n
        return n
    }
}

// ───────────────────────── keep-alive service ─────────────────────────

class KeepAliveService : Service() {
    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        try {
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            val ch = NotificationChannel("lanclip", "LAN Clipboard", NotificationManager.IMPORTANCE_LOW)
            nm.createNotificationChannel(ch)
            val pi = PendingIntent.getActivity(
                this, 0, Intent(this, MainActivity::class.java), PendingIntent.FLAG_IMMUTABLE
            )
            val n = Notification.Builder(this, "lanclip")
                .setContentTitle("LAN Clipboard is running")
                .setContentText("Ready to copy & paste between your devices")
                .setSmallIcon(android.R.drawable.stat_notify_sync)
                .setContentIntent(pi)
                .build()
            startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_DATA_SYNC)
        } catch (e: Exception) {
        }
        CoreHolder.get(applicationContext).start()
        return START_STICKY
    }
}

// ───────────────────────── activity / UI ─────────────────────────

class MainActivity : Activity() {
    private lateinit var core: Core
    private lateinit var statusView: TextView
    private lateinit var titleView: TextView
    private lateinit var listView: ListView
    private val rows = ArrayList<Row>()
    private val adapter = RowAdapter()
    private var pendingPasteId: String? = null
    private var lastSig = ""
    private val REQ_FILES = 11
    private val REQ_FOLDER = 12
    private val clipListener = ClipboardManager.OnPrimaryClipChangedListener {
        try {
            core.sendCurrentClipboard(this)
        } catch (e: Exception) {
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        core = CoreHolder.get(applicationContext)
        buildUi()
        core.onChange = { refresh() }
        core.statusListener = { msg -> statusView.text = msg }
        statusView.text = core.lastStatus
        core.start()
        handleShare(intent)
        try {
            startForegroundService(Intent(this, KeepAliveService::class.java))
        } catch (e: Exception) {
        }
        try {
            if (Build.VERSION.SDK_INT >= 33) {
                requestPermissions(arrayOf("android.permission.POST_NOTIFICATIONS"), 1)
            }
        } catch (e: Exception) {
        }
        refresh()
    }

    override fun onNewIntent(intent: Intent?) {
        super.onNewIntent(intent)
        handleShare(intent)
    }

    override fun onWindowFocusChanged(hasFocus: Boolean) {
        super.onWindowFocusChanged(hasFocus)
        if (hasFocus) {
            try {
                core.sendCurrentClipboard(this)
            } catch (e: Exception) {
            }
        }
    }

    override fun onResume() {
        super.onResume()
        try {
            val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.removePrimaryClipChangedListener(clipListener)
            cm.addPrimaryClipChangedListener(clipListener)
        } catch (e: Exception) {
        }
        core.onChange = { refresh() }
        core.statusListener = { msg -> statusView.text = msg }
        statusView.text = core.lastStatus
        refresh()
    }

    override fun onPause() {
        super.onPause()
        try {
            val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.removePrimaryClipChangedListener(clipListener)
        } catch (e: Exception) {
        }
        core.saveAll()
    }

    override fun onDestroy() {
        super.onDestroy()
        core.onChange = null
        core.statusListener = null
    }

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density + 0.5f).toInt()

    private fun toast(m: String) {
        Toast.makeText(this, m, Toast.LENGTH_SHORT).show()
    }

    private fun mkBtn(label: String, action: () -> Unit): Button {
        val b = Button(this)
        b.text = label
        b.isAllCaps = false
        b.textSize = 13f
        b.setTextColor(Color.WHITE)
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        val bg = GradientDrawable()
        bg.setColor(Color.parseColor("#2D5BD1"))
        bg.cornerRadius = dp(10).toFloat()
        b.background = RippleDrawable(ColorStateList.valueOf(Color.argb(90, 255, 255, 255)), bg, null)
        b.setOnClickListener { action() }
        val lp = LinearLayout.LayoutParams(0, dp(52), 1f)
        lp.setMargins(dp(3), dp(3), dp(3), dp(3))
        b.layoutParams = lp
        return b
    }

    private fun buildUi() {
        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(Color.parseColor("#121212"))
        root.setPadding(dp(6), dp(10), dp(6), dp(6))

        titleView = TextView(this)
        titleView.textSize = 17f
        titleView.setTextColor(Color.WHITE)
        titleView.setTypeface(null, Typeface.BOLD)
        titleView.setPadding(dp(6), dp(2), dp(6), dp(4))
        root.addView(titleView, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        val row1 = LinearLayout(this)
        row1.orientation = LinearLayout.HORIZONTAL
        row1.addView(mkBtn("Copy Files") { openFiles() })
        row1.addView(mkBtn("Copy Text") { copyTextDialog() })
        row1.addView(mkBtn("Clipboard") { sendClipboard() })
        row1.addView(mkBtn("Resend") { core.resend() })
        root.addView(row1, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        val row2 = LinearLayout(this)
        row2.orientation = LinearLayout.HORIZONTAL
        row2.addView(mkBtn("Copy Last") { copyLatest() })
        row2.addView(mkBtn("Clear") { core.clearAll() })
        row2.addView(mkBtn("Name") { nameDialog() })
        row2.addView(mkBtn("Auto Setup") { openAccessSettings() })
        root.addView(row2, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        statusView = TextView(this)
        statusView.textSize = 13f
        statusView.setTextColor(Color.parseColor("#B0BEC5"))
        statusView.setPadding(dp(8), dp(6), dp(8), dp(6))
        root.addView(statusView, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        listView = ListView(this)
        listView.divider = null
        listView.dividerHeight = 0
        listView.adapter = adapter
        listView.setOnItemClickListener { _, _, pos, _ ->
            if (pos >= 0 && pos < rows.size) {
                val r = rows[pos]
                if (r.kind == 1) {
                    val p = core.peers[r.ref]
                    if (p != null) p.selected = !p.selected
                    lastSig = ""
                    refresh()
                } else if (r.kind == 2) {
                    core.removeStaged(r.ref)
                } else if (r.kind == 3) {
                    val bb = core.findBatch(r.ref)
                    if (bb != null) {
                        if (core.putBatchOnClipboard(bb)) {
                            toast("Copied! Now long-press in any app and tap Paste")
                        } else {
                            toast("Could not copy to clipboard")
                        }
                    }
                }
            }
        }
        root.addView(listView, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))

        setContentView(root)
    }

    // ---- list ----

    private fun refresh() {
        titleView.text = "LAN Clipboard  -  " + core.myName
        val list = ArrayList<Row>()
        list.add(Row(0, "DEVICES ON THIS WI-FI (tap to turn on/off)", ""))
        val ps = ArrayList<Peer>(core.peers.values)
        ps.sortBy { it.name }
        if (ps.isEmpty()) {
            list.add(Row(4, "Searching... open this app on your other devices (same Wi-Fi).", ""))
        }
        for (p in ps) {
            val mark = if (p.selected) "●  " else "○  "
            list.add(Row(1, mark + p.name + "   (" + p.ip + ")", p.id))
        }
        list.add(Row(0, "COPIED ON THIS DEVICE (tap to remove)", ""))
        if (core.staged.isEmpty()) {
            list.add(Row(4, "Nothing copied yet. Use Copy Files / Copy Text / Clipboard.", ""))
        }
        for (s in core.staged) {
            if (s.isText) {
                var pv = s.text.replace("\n", " ")
                if (pv.length > 60) pv = pv.substring(0, 60) + "..."
                list.add(Row(2, "📝  " + pv, s.id))
            } else {
                val sz = if (s.size >= 0L) fmtSize(s.size) else "?"
                list.add(Row(2, "📄  " + s.name + "  (" + sz + ")", s.id))
            }
        }
        list.add(Row(0, "RECEIVED (tap a row to put it on your clipboard, then Paste anywhere)", ""))
        if (core.inbox.isEmpty()) {
            list.add(Row(4, "Nothing received yet.", ""))
        }
        val df = SimpleDateFormat("HH:mm:ss", Locale.getDefault())
        for (b in core.inbox) {
            var files = 0
            var texts = 0
            var bytes = 0L
            for (i in b.items) {
                if (i.isText) texts++ else files++
                bytes += i.size
            }
            val t = df.format(Date(b.time))
            list.add(Row(3, "⬇  From " + b.from + "  -  " + files.toString() + " file(s), " + texts.toString() + " text  -  " + fmtSize(bytes) + "  -  " + t, b.id))
        }
        val sb = StringBuilder()
        for (r in list) {
            sb.append(r.kind).append('|').append(r.text).append('|').append(r.ref).append('\n')
        }
        val sig = sb.toString()
        if (sig == lastSig) return
        lastSig = sig
        rows.clear()
        rows.addAll(list)
        adapter.notifyDataSetChanged()
    }

    inner class RowAdapter : BaseAdapter() {
        override fun getCount(): Int = rows.size
        override fun getItem(position: Int): Any = rows[position]
        override fun getItemId(position: Int): Long = position.toLong()
        override fun getView(position: Int, convertView: View?, parent: ViewGroup?): View {
            val tv: TextView = if (convertView is TextView) convertView else TextView(this@MainActivity)
            val r = rows[position]
            tv.text = r.text
            when (r.kind) {
                0 -> {
                    tv.textSize = 12f
                    tv.setTextColor(Color.parseColor("#8AB4F8"))
                    tv.setTypeface(null, Typeface.BOLD)
                    tv.setBackgroundColor(Color.TRANSPARENT)
                    tv.setPadding(dp(8), dp(14), dp(8), dp(4))
                }
                1 -> {
                    tv.textSize = 16f
                    tv.setTextColor(Color.WHITE)
                    tv.setTypeface(null, Typeface.NORMAL)
                    tv.setBackgroundColor(if (r.text.startsWith("●")) Color.parseColor("#1E3A2A") else Color.parseColor("#222222"))
                    tv.setPadding(dp(12), dp(12), dp(12), dp(12))
                }
                2 -> {
                    tv.textSize = 15f
                    tv.setTextColor(Color.WHITE)
                    tv.setTypeface(null, Typeface.NORMAL)
                    tv.setBackgroundColor(Color.parseColor("#222222"))
                    tv.setPadding(dp(12), dp(10), dp(12), dp(10))
                }
                3 -> {
                    tv.textSize = 15f
                    tv.setTextColor(Color.WHITE)
                    tv.setTypeface(null, Typeface.NORMAL)
                    tv.setBackgroundColor(Color.parseColor("#1C2433"))
                    tv.setPadding(dp(12), dp(14), dp(12), dp(14))
                }
                else -> {
                    tv.textSize = 13f
                    tv.setTextColor(Color.parseColor("#9AA0A6"))
                    tv.setTypeface(null, Typeface.NORMAL)
                    tv.setBackgroundColor(Color.TRANSPARENT)
                    tv.setPadding(dp(12), dp(8), dp(12), dp(8))
                }
            }
            return tv
        }
    }

    // ---- actions ----

    private fun openFiles() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
        startActivityForResult(i, REQ_FILES)
    }

    private fun pickFolder() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(
            Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION or
                Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION
        )
        startActivityForResult(i, REQ_FOLDER)
    }

    @Suppress("DEPRECATION")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK || data == null) return
        if (requestCode == REQ_FILES) {
            val uris = ArrayList<Uri>()
            val cd = data.clipData
            if (cd != null) {
                for (k in 0 until cd.itemCount) {
                    val u = cd.getItemAt(k).uri
                    if (u != null) uris.add(u)
                }
            } else {
                val u = data.data
                if (u != null) uris.add(u)
            }
            for (u in uris) {
                try {
                    contentResolver.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION)
                } catch (e: Exception) {
                }
            }
            core.copyFiles(uris, ArrayList<String>())
        } else if (requestCode == REQ_FOLDER) {
            val u = data.data
            if (u != null) {
                try {
                    contentResolver.takePersistableUriPermission(
                        u, Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
                    )
                } catch (e: Exception) {
                }
                core.setFolder(u.toString())
                core.status("Save folder set.")
                val pid = pendingPasteId
                pendingPasteId = null
                if (pid != null) doPaste(pid)
            }
        }
    }

    private fun readClipText(): String {
        try {
            val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            val clip = cm.primaryClip
            if (clip != null && clip.itemCount > 0) {
                val t = clip.getItemAt(0).coerceToText(this)
                if (t != null) return t.toString()
            }
        } catch (e: Exception) {
        }
        return ""
    }

    private fun copyTextDialog() {
        val et = EditText(this)
        et.setText(readClipText())
        et.minLines = 3
        et.gravity = Gravity.TOP
        AlertDialog.Builder(this)
            .setTitle("Copy text to selected devices")
            .setView(et)
            .setPositiveButton("Copy & Send") { _, _ ->
                val t = et.text.toString()
                if (t.isNotEmpty()) core.copyFiles(ArrayList<Uri>(), listOf(t))
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    private fun sendClipboard() {
        try {
            val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            val clip = cm.primaryClip
            if (clip == null || clip.itemCount == 0) {
                toast("Clipboard is empty")
                return
            }
            val uris = ArrayList<Uri>()
            val texts = ArrayList<String>()
            for (k in 0 until clip.itemCount) {
                val item = clip.getItemAt(k)
                val u = item.uri
                if (u != null && u.scheme == "content") {
                    uris.add(u)
                } else {
                    val t = item.coerceToText(this)
                    if (t != null && t.isNotEmpty()) texts.add(t.toString())
                }
            }
            if (uris.isEmpty() && texts.isEmpty()) {
                toast("Clipboard is empty")
                return
            }
            core.copyFiles(uris, texts)
        } catch (e: Exception) {
            toast("Cannot read clipboard")
        }
    }

    private fun nameDialog() {
        val et = EditText(this)
        et.setText(core.myName)
        AlertDialog.Builder(this)
            .setTitle("This device's name")
            .setView(et)
            .setPositiveButton("Save") { _, _ ->
                val t = et.text.toString().trim()
                if (t.isNotEmpty()) core.setName(t)
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    private fun openAccessSettings() {
        toast("Find 'LAN Clipboard auto-detect' and turn it on")
        try {
            startActivity(Intent(Settings.ACTION_ACCESSIBILITY_SETTINGS))
        } catch (e: Exception) {
            toast("Cannot open settings")
        }
    }

    @Suppress("DEPRECATION")
    private fun handleShare(i: Intent?) {
        if (i == null) return
        val a = i.action
        if (a != Intent.ACTION_SEND && a != Intent.ACTION_SEND_MULTIPLE) return
        val uris = ArrayList<Uri>()
        val texts = ArrayList<String>()
        if (a == Intent.ACTION_SEND) {
            val u = i.getParcelableExtra<Uri>(Intent.EXTRA_STREAM)
            if (u != null) {
                uris.add(u)
            } else {
                val t = i.getCharSequenceExtra(Intent.EXTRA_TEXT)
                if (t != null && t.isNotEmpty()) texts.add(t.toString())
            }
        } else {
            val l = i.getParcelableArrayListExtra<Uri>(Intent.EXTRA_STREAM)
            if (l != null) uris.addAll(l)
        }
        if (uris.isEmpty() && texts.isEmpty()) return
        i.action = null
        core.copyFiles(uris, texts)
        toast("Sending to your other devices...")
    }

    private fun copyLatest() {
        if (core.inbox.isEmpty()) {
            toast("Nothing received yet")
            return
        }
        if (core.putBatchOnClipboard(core.inbox[0])) {
            toast("Copied! Now long-press in any app and tap Paste")
        } else {
            toast("Could not copy to clipboard")
        }
    }

    private fun doPaste(batchId: String?) {
        var b: Batch? = null
        for (x in core.inbox) {
            if (batchId == null || x.id == batchId) {
                b = x
                break
            }
        }
        if (b == null) {
            toast("Nothing received yet")
            return
        }
        var needsFolder = false
        for (i in b.items) {
            if (!i.isText) needsFolder = true
        }
        val f = core.folderUri()
        if (needsFolder && f == null) {
            pendingPasteId = b.id
            toast("Choose a folder where pasted files are saved")
            pickFolder()
            return
        }
        core.pasteBatch(b, if (f != null) Uri.parse(f) else null)
    }

    // ---- keyboard shortcuts (buttons are non-focusable so keys reach here) ----

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && event.repeatCount == 0 && event.isCtrlPressed) {
            when (event.keyCode) {
                KeyEvent.KEYCODE_O -> {
                    openFiles()
                    return true
                }
                KeyEvent.KEYCODE_T -> {
                    copyTextDialog()
                    return true
                }
                KeyEvent.KEYCODE_V -> {
                    copyLatest()
                    return true
                }
                KeyEvent.KEYCODE_B -> {
                    sendClipboard()
                    return true
                }
                KeyEvent.KEYCODE_R -> {
                    core.resend()
                    return true
                }
                KeyEvent.KEYCODE_D -> {
                    core.clearAll()
                    return true
                }
            }
        }
        return super.dispatchKeyEvent(event)
    }
}

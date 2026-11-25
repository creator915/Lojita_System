namespace Lojita.Store.TreeCAS.Native

/-- The store and traversal roots are opened once. Operations on children take a
    single raw Linux filename relative to a pinned directory descriptor. -/
@[extern "ljt_open"] opaque openDir (path : @& String) (create : Bool) : IO UInt32
@[extern "ljt_sync_store"] opaque syncStore (fd : UInt32) : IO Unit
@[extern "ljt_close"] opaque closeDir (fd : UInt32) : IO Unit
@[extern "ljt_capture_store"] opaque captureStore (path : @& String) (source : UInt32) : IO UInt32
@[extern "ljt_names"] opaque names (fd : UInt32) : IO (Array ByteArray)
@[extern "ljt_stat"] opaque stamp (parent : UInt32) (name : @& ByteArray) : IO ByteArray
@[extern "ljt_check"] opaque checkStamp (fd : UInt32) (expected : @& ByteArray) : IO Unit
@[extern "ljt_child"] opaque child (parent : UInt32) (name : @& ByteArray) (create : Bool) : IO UInt32
@[extern "ljt_source_bytes"] opaque sourceBytes (parent : UInt32) (name expected : @& ByteArray) : IO ByteArray
@[extern "ljt_get"] opaque getObject (store : UInt32) (kind : UInt8) (digest : @& ByteArray) : IO ByteArray
@[extern "ljt_put"] opaque putObject (store : UInt32) (kind : UInt8) (data : @& ByteArray) : IO ByteArray
@[extern "ljt_emit"] opaque emitFile (dir : UInt32) (name : @& ByteArray) (kind : UInt8) (mode : UInt32)
    (data : @& ByteArray) : IO Unit
@[extern "ljt_mode"] opaque setMode (dir mode : UInt32) : IO Unit
@[extern "ljt_stage"] opaque newStage (parent : UInt32) : IO ByteArray
@[extern "ljt_publish"] opaque publish (parent : UInt32) (stage target : @& ByteArray) : IO Unit
@[extern "ljt_remove"] opaque removeEntry (parent : UInt32) (name : @& ByteArray) : IO Unit

end Lojita.Store.TreeCAS.Native

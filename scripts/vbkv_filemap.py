# files under Impl/
IMPL_FILE_MAP = {"AllocationReport": (["AllocationReport.i.dfy"], ["AllocationReport.i.dfy"]),
"BlockAllocator": (["BlockAllocatorImpl.i.dfy", "BlockAllocatorModel.i.dfy"], ["BlockAllocatorImpl.i.dfy", "BlockAllocatorModel.i.dfy"]),
"Bookkeeping": (["BookkeepingImpl.i.dfy", "BookkeepingModel.i.dfy"], ["BookkeepingImpl.i.dfy", "BookkeepingModel.i.dfy"]),
"BucketGenerator": (["BucketGeneratorImpl.i.dfy", "BucketGeneratorModel.i.dfy"], ["BucketGeneratorImpl.i.dfy", "BucketGeneratorModel.i.dfy"]),
"BucketSuccessorLoop": (["BucketSuccessorLoopImpl.i.dfy", "BucketSuccessorLoopModel.i.dfy"], ["BucketSuccessorLoopImpl.i.dfy", "BucketSuccessorLoopModel.i.dfy"]),
"Bundle": (["Bundle.i.dfy"], ["Bundle.i.dfy"]),
"Cache": (["CacheImpl.i.dfy"], ["CacheImpl.i.dfy"]),
"Committer":(["CommitterAppendImpl.i.dfy", "CommitterAppendModel.i.dfy", "CommitterCommitImpl.i.dfy", "CommitterCommitModel.i.dfy", "CommitterImpl.i.dfy", "CommitterInitImpl.i.dfy","CommitterInitModel.i.dfy", "CommitterModel.i.dfy", "CommitterReplayImpl.i.dfy", "CommitterReplayModel.i.dfy"], ["CommitterImpl.i.dfy"]),
"Coordination": (["CoordinationImpl.i.dfy", "CoordinationModel.i.dfy"], ["CoordinationImpl.i.dfy"]),
"Dealloc": (["DeallocImpl.i.dfy", "DeallocModel.i.dfy"], ["DeallocImpl.i.dfy"]),
"DiskOp": (["DiskOpImpl.i.dfy", "DiskOpModel.i.dfy"], ["DiskOpImpl.i.dfy", "DiskOpModel.i.dfy"]),
"Evict": (["EvictImpl.i.dfy", "EvictModel.i.dfy"], ["EvictImpl.i.dfy"]),
"Flush": (["FlushImpl.i.dfy", "FlushModel.i.dfy"], ["FlushImpl.i.dfy", "FlushModel.i.dfy"]),
"FlushPolicy": (["FlushPolicyImpl.i.dfy", "FlushPolicyModel.i.dfy"], ["FlushPolicyImpl.i.dfy", "FlushPolicyModel.i.dfy"]),
"Full": (["FullImpl.i.dfy"], ["FullImpl.i.dfy"]),
"Grow": (["GrowImpl.i.dfy", "GrowModel.i.dfy"], ["GrowImpl.i.dfy", "GrowModel.i.dfy"]),
"HandleReadResponse": (["HandleReadResponseImpl.i.dfy", "HandleReadResponseModel.i.dfy"], ["HandleReadResponseImpl.i.dfy", "HandleReadResponseModel.i.dfy"]),
"HandleWriteResponse": (["HandleWriteResponseImpl.i.dfy", "HandleWriteResponseModel.i.dfy"], ["HandleWriteResponseImpl.i.dfy"]),
"IO": (["IOImpl.i.dfy", "IOModel.i.dfy"], ["IOImpl.i.dfy", "IOModel.i.dfy"]),
"IndirectionTable": (["IndirectionTableImpl.i.dfy", "IndirectionTableModel.i.dfy"], ["IndirectionTable.i.dfy"]),
"Insert": (["InsertImpl.i.dfy", "InsertModel.i.dfy"], ["InsertImpl.i.dfy", "InsertModel.i.dfy"]),
"Journalist": (["JournalistImpl.i.dfy", "JournalistModel.i.dfy"], ["JournalistImpl.i.dfy"]),
"JournalistMarshalling": (["JournalistMarshallingImpl.i.dfy", "JournalistMarshallingModel.i.dfy"], ["JournalistMarshallingImpl.i.dfy", "JournalistMarshallingModel.i.dfy"]),
"JournalistParsing": (["JournalistParsingImpl.i.dfy"], ["JournalistParsingImpl.i.dfy"]),
"Leaf": (["LeafImpl.i.dfy", "LeafModel.i.dfy"], ["LeafImpl.i.dfy", "LeafModel.i.dfy"]),
"Main": (["Main.s.dfy"], ["Main.s.dfy"]),
"MainDiskIOHandler": (["MainDiskIOHandler.s.dfy"], ["MainDiskIOHandler.s.dfy"]),
"MainHandlers": (["MainHandlers.i.dfy"], ["MainHandlers.i.dfy"]),
"Mkfs": (["Mkfs.i.dfy", "MkfsModel.i.dfy"], ["Mkfs.i.dfy", "MkfsModel.i.dfy"]),
"Node": (["NodeImpl.i.dfy", "NodeModel.i.dfy"], ["NodeImpl.i.dfy"]),
"Query": (["QueryImpl.i.dfy", "QueryModel.i.dfy"], ["QueryImpl.i.dfy", "QueryModel.i.dfy"]),
"Split": (["SplitImpl.i.dfy", "SplitModel.i.dfy"], ["SplitImpl.i.dfy", "SplitModel.i.dfy"]),
"State": (["StateImpl.i.dfy", "StateModel.i.dfy"], ["StateBCImpl.i.dfy", "StateSectorImpl.i.dfy"]),
"Succ": (["SuccImpl.i.dfy", "SuccModel.i.dfy"], ["SuccImpl.i.dfy", "SuccModel.i.dfy"]),
"Sync": (["SyncImpl.i.dfy", "SyncModel.i.dfy"], ["SyncImpl.i.dfy"])}

# impl files under lib/DataStructures
DS_FILE_MAP = {
    "Bitmap": (["BitmapImpl.i.dfy", "BitmapModel.i.dfy"],["BitmapImpl.i.dfy", "BitmapModel.i.dfy"]),
    "Btree": (["BtreeModel.i.dfy", "KMBtree.i.dfy", "MutableBtree.i.dfy"], ["BtreeModel.i.dfy", "KMBtree.i.dfy", "MutableBtree.i.dfy"]),
    # "Btree": (["KMBtree.i.dfy"], ["KMBtree.i.dfy"]),
    "Lru": (["LruImpl.i.dfy", "LruModel.i.dfy"], ["LinearLru.i.dfy", "LruModel.i.dfy", "LinearDList.i.dfy", "LinearUSeq.i.dfy"]),
    "Map": (["MutableMapImpl.i.dfy", "MutableMapModel.i.dfy"], ["LinearMutableMap.i.dfy", "LinearMutableMapBase.i.dfy", "LinearContentMutableMap.i.dfy"])
}

# impl files under lib/Marshalling
MARSHALLING_FILE_MAP = {
    "Marshalling": (
        ["GenericMarshalling.i.dfy", "MarshallingImpl.i.dfy", "MarshallingModel.i.dfy", "Maps.i.dfy", "Native.s.dfy", "Seqs.i.dfy", "Util.i.dfy"],
        ["GenericMarshalling.i.dfy", "MarshallingImpl.i.dfy", "MarshallingModel.i.dfy", "Maps.i.dfy", "Native.s.dfy", "Seqs.i.dfy", "Util.i.dfy"],
    )
}

# impl files under lib/Buckets
BUCKETS_FILE_MAP = {
    "Bucket": (["BucketImpl.i.dfy", "BucketIteratorModel.i.dfy"], ["BucketImpl.i.dfy", "BucketIteratorModel.i.dfy"]),
    "KV": (["KMBPKVOps.i.dfy"], ["LKMBPKVOps.i.dfy"]),
    "Packed": (["PackedKV.i.dfy", "PackedKVMarshalling.i.dfy","PackedStringArray.i.dfy", "PackedStringArrayMarshalling.i.dfy"], ["PackedKV.i.dfy", "PackedKVMarshalling.i.dfy","PackedStringArray.i.dfy","PackedStringArrayMarshalling.i.dfy"])
}

FILE_MAP = dict()
FILE_MAP.update(IMPL_FILE_MAP)
FILE_MAP.update(DS_FILE_MAP)
FILE_MAP.update(MARSHALLING_FILE_MAP)
FILE_MAP.update(BUCKETS_FILE_MAP)

COMPONENT_MAP = {
    "TreeOps": ["BucketGenerator", "BucketSuccessorLoop", "Flush", "Grow", "Insert", "Leaf", "Node", "Query", "Split", "Succ", ],
    "Journal": ["Journalist", "JournalistMarshalling", "JournalistParsing", ],
    "LookupTable": ["Bookkeeping","Dealloc", "Evict", "IndirectionTable", ],
    "IO": ["IO", "HandleReadResponse", "HandleWriteResponse", "Full", "DiskOp", "MainDiskIOHandler", "Sync", "Committer"],
    "SystemCoord.": ["State", "Mkfs", "Coordination", "FlushPolicy"],
    "Buckets": ["Bucket", "KV", "Packed"],
    "LibDS": ["Bitmap", "Btree", "Lru", "Map"],
    "Other":["AllocationReport", "BlockAllocator", "Marshalling", "Cache", "Main", "MainHandlers", "Bundle"]
}

CHANGES_MAP = {
    "Linear Only": ["AllocationReport", "BlockAllocator", "Bookkeeping", "BucketGenerator", "BucketSuccessorLoop", "Bundle", 
        "DiskOp", "Flush", "FlushPolicy", "Full", "Grow", "HandleReadResponse", "IO", "Insert", "JournalistParsing", "JournalistMarshalling",
        "Leaf", "Main", "MainDiskIOHandler", "MainHandlers", "Mkfs", "Query", "Split", "Succ", "Bitmap", "Btree", "Marshalling","Bucket","KV"],
    "Linear & Model/Impl Merge": ["Committer", "Coordination", "Dealloc", "Evict", "HandleWriteResponse", "IndirectionTable", "Journalist", "Node", "State", "Sync"],
    "Linear & Impl Changes": ["Cache", "Map", "Lru"],
    "Unchanged": ["Packed"]
}

REPO_NAMES = ["veribetrkv-dynamic-frames", "veribetrkv-linear"]

# PER_FILE_JSON = "file_time.json"
# PER_PROC_JSON = "proc_time.json"

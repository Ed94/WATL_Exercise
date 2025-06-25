/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, MSVC & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: odin-lang/Odin dev-2025-06
*/
package odin

main :: proc()
{
	
}

import "base:builtin"
import "base:intrinsics"

//#region("Package Mappings")
abs   :: builtin.abs
min   :: builtin.min
max   :: builtin.max
clamp :: builtin.clamp

copy :: proc {
	memory_copy,
	slice_copy,
}
copy_non_overlapping :: proc {
	memory_copy_non_overlapping,
	slice_copy_non_overlapping,
}
end :: proc {
	slice_end,
}
zero :: proc {
	memory_zero,
	slice_zero,
}
zero_explicit :: proc {
	memory_zero_explicit,
}
//#endregion("Package Mappings")

//#region("Memory")
align_pow2 :: proc(x: int, b: int) -> int {
    assert(b != 0)
    assert((b & (b - 1)) == 0) // Check power of 2
    return ((x + b - 1) & ~(b - 1))
}
memory_zero :: proc "contextless" (data: rawptr, len: int) -> rawptr {
	intrinsics.mem_zero(data, len)
	return data
}
memory_zero_explicit :: proc "contextless" (data: rawptr, len: int) -> rawptr {
	intrinsics.mem_zero_volatile(data, len) // Use the volatile mem_zero
	intrinsics.atomic_thread_fence(.Seq_Cst) // Prevent reordering
	return data
}
memory_copy :: proc "contextless" (dst, src: rawptr, len: int) -> rawptr {
	intrinsics.mem_copy(dst, src, len)
	return dst
}
memory_copy_non_overlapping :: proc "contextless" (dst, src: rawptr, len: int) -> rawptr {
	intrinsics.mem_copy_non_overlapping(dst, src, len)
	return dst
}

Raw_Slice :: struct {
	data: rawptr,
	len:  int,
}
slice_assert :: proc "contextless" (s: $Type / []$SliceType) -> Type {
	return assert(len(s) > 0) && s != nil
}
slice_end :: proc "contextless" (s : $Type / []$SliceType) -> Type {
	return s[len(s) - 1]
}
size_of_slice_type :: proc "contextless" (slice: $Type / []$SliceType) -> int {
    return size_of(E)
}
@(require_results)
to_bytes :: proc "contextless" (s: []$Type) -> []byte {
	return ([^]byte)(raw_data(s))[:len(s) * size_of(T)]
}
slice_zero :: proc "contextless" (data: $Type / []$SliceType) -> Type {
	zero(raw_data(data), size_of(E) * len(data))
	return data
}
slice_copy :: proc "contextless" (dst, src: $Ttype / []$SliceType) -> int {
	n := max(0, min(len(dst), len(src)))
	if n > 0 {
		intrinsics.mem_copy(raw_data(dst), raw_data(src), n*size_of(E))
	}
	return n
}
slice_copy_non_overlapping :: proc "contextless" (dst, src: $Type / []$SliceType) -> int {
	n := max(0, min(len(dst), len(src)))
	if n > 0 {
		intrinsics.mem_copy_non_overlapping(raw_data(dst), raw_data(src), n*size_of(E))
	}
	return n
}

sll_stack_push_n :: proc "contextless" (first: ^$SLL_NodeType, n: ^SLL_NodeType) {
    n.next = first^
    first^ = n
}
sll_queue_push_nz :: proc(nil_val: ^$SLL_NodeType, first: ^SLL_NodeType, last: ^SLL_NodeType, n: ^SLL_NodeType) {
	if first^ == nil_val {
		first^ = n
		last^ = n
		n.next = nil_val
	} else {
		last^.next = n
		last^ = n
		n.next = nil_val
	}
}
sll_queue_push_n :: proc "contextless" (first: ^$SLL_NodeType, last: ^SLL_NodeType, n: ^SLL_NodeType) {
    sll_queue_push_nz(nil, first, last, n)
}
//#endregion("Memory")

//#region Allocator Interface
AllocatorOp :: enum u32 {
	Alloc_NoZero = 0, // If Alloc exist, so must No_Zero
	Alloc,
	Free,
	Reset,
	Grow_NoZero,
	Grow,
	Shrink,
	Rewind,
	SavePoint,
	Query, // Must always be implemented
}
AllocatorQueryFlag :: enum u64 {
	AllocatorQuery_Alloc,
	AllocatorQuery_Free,
	// Wipe the allocator's state
	AllocatorQuery_Reset,
	// Supports both grow and shrink
	AllocatorQuery_Shrink,
	AllocatorQuery_Grow,
	// Ability to rewind to a save point (ex: arenas, stack), must also be able to save such a point
	AllocatorQuery_Rewind,
}
AllocatorQueryFlags :: bit_set[AllocatorQueryFlag; u64]
AllocatorSP :: struct {
	type_sig: ^AllocatorProc,
	slot:     int,
}
AllocatorProc :: #type proc (input: AllocatorProc_In, out: ^AllocatorProc_Out)
AllocatorProc_In :: struct {
	data:           rawptr,
	requested_size: int,
	alignment:      int,
	old_allocation: []byte,
	op:             AllocatorOp,
}
AllocatorProc_Out :: struct {
	using _ : struct #raw_union {
		allocation: []byte,
		save_point: AllocatorSP,
	},
	features:         AllocatorQueryFlags,
	left:             int,
	max_alloc:        int,
	min_alloc:        int,
	continuity_break: b32,
}
AlllocatorQueryInfo :: struct {
	save_point:       AllocatorSP,
	features:         AllocatorQueryFlags,
	left:             int,
	max_alloc:        int,
	min_alloc:        int,
	continuity_break: b32,
}
AllocatorInfo :: struct {
	procedure: AllocatorProc,
	data:      rawptr,
}
// #assert(size_of(AllocatorQueryInfo) == size_of(AllocatorProc_Out))

MEMORY_ALIGNMENT_DEFAULT :: 2 * size_of(rawptr)

allocator_query :: proc(ainfo: AllocatorInfo) -> AlllocatorQueryInfo {

}
mem_free :: proc(ainfo: AllocatorInfo, mem: []byte) {

}
mem_reset :: proc(ainfo: AllocatorInfo) {

}
mem_rewind :: proc(ainfo: AllocatorInfo, save_point: AllocatorSP) {

}
mem_save_point :: proc(ainfo: AllocatorInfo) -> AllocatorSP {

}
mem_alloc :: proc(ainfo: AllocatorInfo, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {

}
mem_grow :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {

}
mem_resize :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {

}
mem_shrink :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {

}

alloc_type  :: proc(ainfo: AllocatorInfo, $Type: typeid) -> []Type {

}
alloc_slice :: proc(ainfo: AllocatorInfo, $Type: typeid, num : int) -> []Type {

}
//#endregion Allocator Interface

//#region("Strings")
Raw_String :: struct {
	data: [^]byte,
	len:  int,
}
//#endregion("Strings")


//#region("FArena")
FArena :: struct {
	mem:  []byte,
	used: int,
}
farena_make :: proc(backing: []byte) -> FArena { arena := FArena {mem = backing}; return arena }
farena_init :: proc(arena: ^FArena, backing: []byte) {

}
farena_push :: proc(arena: ^FArena, $Type: typeid, amount: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []Type {

}
farena_reset :: proc(arena: ^FArena) {
	arena.used = 0
}
farena_rewind :: proc(arena: ^FArena, save_point: AllocatorSP) {

}
farena_save :: proc(arena: FArena) -> AllocatorSP {

}
farena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {

}
//#endregion("FArena")

//#region("OS")
OS_SystemInfo :: struct {
	target_page_size: int,
}
os_init :: proc() {

}
os_system_info :: proc() {

}
os_vmem_commit :: proc(vm: rawptr, size: int, no_large_pages: b32 = false) {

}
os_vmem_reserve :: proc(size: int, base_addr: int = 0, no_large_pages: b32 = false) -> rawptr {

}
os_vmem_release :: proc(vm : rawptr, size: int) {

}
//#endregion("OS")

//#region("VArena")
VArenaFlag :: enum u32 {
	No_Large_Pages,
}
VArenaFlags :: bit_set[VArenaFlag; u32]
VArena :: struct {
	reserve_start: int,
	reserve:       int,
	commit_size:   int,
	committed:     int,
	commit_used:   int,
	flags:         VArenaFlags,
}
varena_make :: proc(base_addr, reserve_size, commit_size: int, flags: VArenaFlags) -> VArena {

}
varena_push :: proc(va: ^VArena, $Type: typeid, amount: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []Type {

}
varena_release :: proc(va: ^VArena) {

}
varena_rewind :: proc(va: ^VArena) {

}
varena_shrink :: proc(va: ^VArena) {

}
varena_save :: proc(va: ^VArena) {

}
varena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {

}
//#endregion("VArena")

//#region("Arena (Casey-Ryan Composite Arena")
ArenaFlag :: enum u32 {
	No_Large_Pages,
	No_Chaining,
}
ArenaFlags :: bit_set[ArenaFlag; u32]
Arena :: struct {
	backing:  ^VArena,
	prev:     ^Arena,
	curr:     ^Arena,
	base_pos: int,
	pos:      int,
	flags:    ArenaFlags,
}
arena_make :: proc()
arena_push :: proc()
arena_release :: proc()
arena_reset :: proc()
arena_rewind :: proc()
arena_save :: proc()
arena_allocator_proc :: proc(input: AllocatorProc_In, output: AllocatorProc_Out)
//#endregion("Arena (Casey-Ryan Composite Arena")

//#region("Hashing")
hash64_djb8 :: proc() {}
//#endregion("Hashing")

//#region("Key Table 1-Layer Linear (KT1L)")
KT1L_Slot :: struct($type: typeid) {
	key:   u64,
	value: type
}
KT1L_Meta :: struct {
	slot_size:       int,
	kt_value_offset: int,
	type_width:      int,
	type_name:       string,
}
kt1l_populate_slice_a2_Slice_Byte :: proc(kt: ^[]KT1L_Slot(byte), m: KT1L_Meta, backing: AllocatorInfo, values: []byte, num_values: []byte) {

}
kt1l_populate_slice_a2 :: proc($Type: typeid, kt: ^[]KT1L_Slot(Type), backing: AllocatorInfo, values: [][2]Type) {

}
//#endregion("Key Table 1-Layer Linear (KT1L)")

//#region("Key Table 1-Layer Chained-Chunked-Cells (KT1CX)")

//#endregion("Key Table 1-Layer Chained-Chunked-Cells (KT1CX)")

//#region("String Operations")
//#endregion("String Operations")

//#region("File System")
//#endregion("File System")

//#region("WATL")
//#endregion("WATL")

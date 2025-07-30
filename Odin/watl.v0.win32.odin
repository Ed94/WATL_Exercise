/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: odin-lang/Odin dev-2025-07
*/
package odin

import "base:builtin"
import "base:intrinsics"
import "base:runtime"

//region Package Mappings
abs   :: builtin.abs
min   :: builtin.min
max   :: builtin.max
clamp :: builtin.clamp

ainfo :: proc {
	farena_ainfo,
	varena_ainfo,
	arena_ainfo,
}
alloc :: proc {
	mem_alloc,
	alloc_type,
	alloc_slice,
}
copy :: proc {
	memory_copy,
	slice_copy,
	string_copy,
}
copy_non_overlapping :: proc {
	memory_copy_non_overlapping,
	slice_copy_non_overlapping,
}
cursor :: proc {
	ptr_cursor,
	slice_cursor,
	string_cursor,
}
end :: proc {
	slice_end,
	string_end,
}
push :: proc {
	farena_push,
	varena_push,
	arena_push,
}
reset :: proc {
	farena_reset,
	varena_reset,
	arena_reset,
}
save :: proc {
	farena_save,
	varena_save,
	arena_save,
}
to_bytes :: proc {
	slice_to_bytes,
}
raw :: proc {
	slice_raw,
}
zero :: proc {
	memory_zero,
	slice_zero,
}
zero_explicit :: proc {
	memory_zero_explicit,
}

file_read_contents :: proc {
	api_file_read_contents,
	file_read_contents_stack,
}
watl_lex :: proc {
	api_watl_lex,
	watl_lex_stack,
}
watl_parse :: proc {
	api_watl_parse,
	watl_parse_stack,
}
//endregion Package Mappings

//region Memory
Kilo :: 1024
Mega :: Kilo * 1024
Giga :: Mega * 1024
Tera :: Giga * 1024

ptr_cursor :: #force_inline proc "contextless" (ptr: ^$Type) -> [^]Type { return transmute([^]Type) ptr }

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

SliceByte :: struct {
	data: [^]byte,
	len: int
}
SliceRaw  :: struct ($Type: typeid) {
	data: [^]Type,
	len:  int,
}
slice        :: #force_inline proc "contextless" (s: [^] $Type, num: $Some_Integer) -> [ ]Type { return transmute([]Type) SliceRaw(Type) { s, cast(int) num } }
slice_cursor :: #force_inline proc "contextless" (s: []$Type)                       -> [^]Type { return transmute([^]Type) raw_data(s) }
slice_assert :: #force_inline proc (s: $SliceType / []$Type) {
	assert(len(s) > 0)
	assert(s != nil)
}
slice_end :: #force_inline proc "contextless" (s : $SliceType / []$Type) -> ^Type { return & cursor(s)[len(s)] }

@(require_results) slice_to_bytes :: proc "contextless" (s: []$Type) -> []byte         { return ([^]byte)(raw_data(s))[:len(s) * size_of(Type)] }
@(require_results) slice_raw      :: proc "contextless" (s: []$Type) -> SliceRaw(Type) { return transmute(SliceRaw(Type)) s }

slice_zero :: proc "contextless" (data: $SliceType / []$Type) { memory_zero(raw_data(data), size_of(Type) * len(data)) }
slice_copy :: proc "contextless" (dst, src: $SliceType / []$Type) -> int {
	n := max(0, min(len(dst), len(src)))
	if n > 0 {
		intrinsics.mem_copy(raw_data(dst), raw_data(src), n * size_of(Type))
	}
	return n
}
slice_copy_non_overlapping :: proc "contextless" (dst, src: $SliceType / []$Type) -> int {
	n := max(0, min(len(dst), len(src)))
	if n > 0 {
		intrinsics.mem_copy_non_overlapping(raw_data(dst), raw_data(src), n * size_of(Type))
	}
	return n
}

sll_stack_push_n :: proc "contextless" (curr, n, n_link: ^^$Type) {
    (n_link ^) = (curr ^)
    (curr   ^) = (n    ^)
}
sll_queue_push_nz :: proc "contextless" (first: ^$ParentType, last, n: ^^$Type, nil_val: ^Type) {
	if (first ^) == nil_val {
		(first ^) = n^
		(last  ^) = n^
		n^.next = nil_val
	}
	else {
		(last ^).next = n^
		(last ^)      = n^
		n^.next        = nil_val
	}
}
sll_queue_push_n :: #force_inline proc "contextless" (first: $ParentType, last, n: ^^$Type) { sll_queue_push_nz(first, last, n, nil) }
//endregion Memory

//region Allocator Interface
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
	Alloc,
	Free,
	// Wipe the allocator's state
	Reset,
	// Supports both grow and shrink
	Shrink,
	Grow,
	// Ability to rewind to a save point (ex: arenas, stack), must also be able to save such a point
	Rewind,
}
AllocatorQueryFlags :: bit_set[AllocatorQueryFlag; u64]
AllocatorSP :: struct {
	type_sig: AllocatorProc,
	slot:     int,
}
AllocatorProc :: #type proc (input: AllocatorProc_In, out: ^AllocatorProc_Out)
AllocatorProc_In :: struct {
	data:             rawptr,
	requested_size:   int,
	alignment:        int,
	using _ : struct #raw_union {
		old_allocation: []byte,
		save_point    : AllocatorSP,
	},
	op:               AllocatorOp,
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
AllocatorQueryInfo :: struct {
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

allocator_query :: proc(ainfo: AllocatorInfo) -> AllocatorQueryInfo {
	assert(ainfo.procedure != nil)
	out: AllocatorQueryInfo; ainfo.procedure({data = ainfo.data, op = .Query}, transmute(^AllocatorProc_Out) & out)
	return out
}
mem_free :: proc(ainfo: AllocatorInfo, mem: []byte) {
	assert(ainfo.procedure != nil)
	ainfo.procedure({data = ainfo.data, op = .Free, old_allocation = mem}, & {})
}
mem_reset :: proc(ainfo: AllocatorInfo) {
	assert(ainfo.procedure != nil)
	ainfo.procedure({data = ainfo.data, op = .Reset}, &{})
}
mem_rewind :: proc(ainfo: AllocatorInfo, save_point: AllocatorSP) {
	assert(ainfo.procedure != nil)
	ainfo.procedure({data = ainfo.data, op = .Rewind, save_point = save_point}, & {})
}
mem_save_point :: proc(ainfo: AllocatorInfo) -> AllocatorSP {
	assert(ainfo.procedure != nil)
	out: AllocatorProc_Out
	ainfo.procedure({data = ainfo.data, op = .SavePoint}, & out)
	return out.save_point
}
mem_alloc :: proc(ainfo: AllocatorInfo, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = no_zero ? .Alloc_NoZero : .Alloc,
		requested_size = size,
		alignment      = alignment,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return output.allocation
}
mem_grow :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = no_zero ? .Grow_NoZero : .Grow,
		requested_size = size,
		alignment      = alignment,
		old_allocation = mem,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return output.allocation
}
mem_resize :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = len(mem) < size ? .Shrink :  no_zero ? .Grow_NoZero : .Grow,
		requested_size = size,
		alignment      = alignment,
		old_allocation = mem,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return output.allocation
}
mem_shrink :: proc(ainfo: AllocatorInfo, mem: []byte, size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []byte {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = .Shrink,
		requested_size = size,
		alignment      = alignment,
		old_allocation = mem,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return output.allocation
}

alloc_type  :: proc(ainfo: AllocatorInfo, $Type: typeid, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> ^Type {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = no_zero ? .Alloc_NoZero : .Alloc,
		requested_size = size_of(Type),
		alignment      = alignment,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return transmute(^Type) raw_data(output.allocation)
}
alloc_slice :: proc(ainfo: AllocatorInfo, $SliceType: typeid / []$Type, num : int, alignment: int = MEMORY_ALIGNMENT_DEFAULT, no_zero: b32 = false) -> []Type {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = no_zero ? .Alloc_NoZero : .Alloc,
		requested_size = size_of(Type) * num,
		alignment      = alignment,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return transmute([]Type) slice(raw_data(output.allocation), num)
}
//endregion Allocator Interface

//region Strings
Raw_String :: struct {
	data: [^]byte,
	len:     int,
}
string_cursor :: proc(s: string) -> [^]u8 { return slice_cursor(transmute([]byte) s) }
string_copy   :: proc(dst, src: string)   { slice_copy  (transmute([]byte) dst, transmute([]byte) src) }
string_end    :: proc(s: string) -> ^u8   { return slice_end (transmute([]byte) s) }
string_assert :: proc(s: string)          { slice_assert(transmute([]byte) s) }
//endregion Strings

//region FArena
FArena :: struct {
	mem:  []byte,
	used:   int,
}
farena_make :: proc(backing: []byte) -> FArena { 
	arena := FArena {mem = backing}
	return arena 
}
farena_init :: proc(arena: ^FArena, backing: []byte) {
	assert(arena != nil)
	arena.mem  = backing
	arena.used = 0
}
farena_push :: proc(arena: ^FArena, $Type: typeid, amount: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []Type {
	assert(arena != nil)
	if amount == 0 {
		return {}
	}
	desired   := size_of(Type) * amount
	to_commit := align_pow2(desired, alignment)
	unused    := len(arena.mem) - arena.used
	assert(to_commit <= unused)
	ptr        := cursor(arena.mem[arena.used:])
	arena.used += to_commit
	return slice(ptr, amount)
}
farena_reset :: proc(arena: ^FArena) {
	arena.used = 0
}
farena_rewind :: proc(arena: ^FArena, save_point: AllocatorSP) {
	assert(save_point.type_sig  == farena_allocator_proc)
	assert(save_point.slot >= 0 && save_point.slot <= arena.used)
	arena.used = save_point.slot
}
farena_save :: #force_inline proc(arena: FArena) -> AllocatorSP { return AllocatorSP { type_sig = farena_allocator_proc, slot = arena.used } }
farena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	arena := transmute(^FArena) input.data
	
	switch input.op 
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = to_bytes(farena_push(arena, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(output.allocation)
		}
		
	case .Free:
		// No-op for arena
		
	case .Reset:
		farena_reset(arena)
		
	case .Grow, .Grow_NoZero:
		// Check if the allocation is at the end of the arena
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := end(input.old_allocation)
		arena_end := cursor(arena.mem)[arena.used:]
		if alloc_end != arena_end {
			// Not at the end, can't grow in place
			output.allocation = {}
			break
		}
		// Calculate growth
		grow_amount  := input.requested_size - len(input.old_allocation)
		aligned_grow := align_pow2(grow_amount, input.alignment)
		unused       := len(arena.mem) - arena.used
		if aligned_grow > unused {
			// Not enough space
			output.allocation = {}
			break
		}
		arena.used += aligned_grow
		output.allocation = slice(cursor(input.old_allocation), input.requested_size)
		if input.op == .Grow {
			zero(cursor(output.allocation)[len(input.old_allocation):], grow_amount)
		}
		
	case .Shrink:
		// Check if the allocation is at the end of the arena
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := end(input.old_allocation)
		arena_end := cursor(arena.mem)[arena.used:]
		if alloc_end != arena_end {
			// Not at the end, can't shrink but return adjusted size
			output.allocation = input.old_allocation[:input.requested_size]
			break
		}
		// Calculate shrinkage
		aligned_original := align_pow2(len(input.old_allocation), MEMORY_ALIGNMENT_DEFAULT)
		aligned_new      := align_pow2(input.requested_size, input.alignment)
		arena.used       -= (aligned_original - aligned_new)
		output.allocation = input.old_allocation[:input.requested_size]
		
	case .Rewind:
		farena_rewind(arena, input.save_point)
		
	case .SavePoint:
		output.save_point = farena_save(arena^)
		
	case .Query:
		output.features   = {.Alloc, .Reset, .Grow, .Shrink, .Rewind}
		output.max_alloc  = len(arena.mem) - arena.used
		output.min_alloc  = 0
		output.left       = output.max_alloc
		output.save_point = farena_save(arena^)
	}
}
farena_ainfo :: #force_inline proc "contextless" (arena : ^FArena) -> AllocatorInfo { return AllocatorInfo{farena_allocator_proc, arena} }
//endregion FArena

//region OS
OS_SystemInfo :: struct {
	target_page_size: int,
}
OS_Windows_State :: struct {
	system_info: OS_SystemInfo,
}
@(private)
os_windows_info: OS_Windows_State

// Windows API constants
MS_INVALID_HANDLE_VALUE    :: ~uintptr(0)
MS_MEM_COMMIT              :: 0x00001000
MS_MEM_RESERVE             :: 0x00002000
MS_MEM_LARGE_PAGES         :: 0x20000000
MS_MEM_RELEASE             :: 0x00008000
MS_PAGE_READWRITE          :: 0x04
MS_TOKEN_ADJUST_PRIVILEGES :: 0x0020
MS_SE_PRIVILEGE_ENABLED    :: 0x00000002
MS_TOKEN_QUERY             :: 0x0008
// Windows API types
MS_BOOL                  :: i32
MS_DWORD                 :: u32
MS_HANDLE                :: rawptr
MS_LPVOID                :: rawptr
MS_LPCSTR                :: cstring
MS_LPWSTR                :: [^]u16
MS_LPDWORD               :: ^MS_DWORD
MS_LPSECURITY_ATTRIBUTES :: ^MS_SECURITY_ATTRIBUTES
MS_LPOVERLAPPED          :: ^MS_OVERLAPPED
MS_LONG                  :: i32
MS_LONGLONG              :: i64
MS_ULONG_PTR             :: u64
MS_LARGE_INTEGER         :: struct #raw_union { _: struct {LowPart: MS_DWORD, HighPart: MS_LONG}, u: struct {LowPart: MS_DWORD, HighPart: MS_LONG}, QuadPart: MS_LONGLONG }
MS_LUID                  :: struct { low_part: MS_DWORD, high_part: i32 }
MS_LUID_AND_ATTRIBUTES   :: struct { luid: MS_LUID, attributes: MS_DWORD }
MS_TOKEN_PRIVILEGES      :: struct { privilege_count: MS_DWORD, privileges: [1]MS_LUID_AND_ATTRIBUTES }
MS_SECURITY_ATTRIBUTES   :: struct { nLength: MS_DWORD,lpSecurityDescriptor: MS_LPVOID, bInheritHandle: MS_BOOL }
MS_OVERLAPPED            :: struct { Internal: MS_ULONG_PTR, InternalHigh: MS_ULONG_PTR, _: struct #raw_union { LowPart: MS_DWORD, HighPart: MS_LONG }, QuadPart: MS_LONGLONG }
// Windows API imports
foreign import kernel32 "system:Kernel32.lib"
foreign import advapi32 "system:Advapi32.lib"
@(default_calling_convention="stdcall")
foreign kernel32 {
	CloseHandle         :: proc(handle: MS_HANDLE) -> MS_BOOL ---
	GetCurrentProcess   :: proc() -> MS_HANDLE ---
	GetLargePageMinimum :: proc() -> uintptr ---
	VirtualAlloc        :: proc(address: MS_LPVOID, size: uintptr, allocation_type: MS_DWORD, protect: MS_DWORD) -> MS_LPVOID ---
	VirtualFree         :: proc(address: MS_LPVOID, size: uintptr, free_type: MS_DWORD) -> MS_BOOL ---
}
@(default_calling_convention="stdcall")
foreign advapi32 {
	AdjustTokenPrivileges :: proc(token_handle: MS_HANDLE, disable_all: MS_BOOL, new_state: ^MS_TOKEN_PRIVILEGES, buffer_length: MS_DWORD, previous_state: ^MS_TOKEN_PRIVILEGES, return_length: ^MS_DWORD) -> MS_BOOL ---
	LookupPrivilegeValueW :: proc(system_name: MS_LPWSTR, name: MS_LPWSTR, luid: ^MS_LUID) -> MS_BOOL ---
	OpenProcessToken      :: proc(process_handle: MS_HANDLE, desired_access: MS_DWORD, token_handle: ^MS_HANDLE) -> MS_BOOL ---
}

os_enable_large_pages :: proc() {
	token: MS_HANDLE
	if OpenProcessToken(GetCurrentProcess(), MS_TOKEN_ADJUST_PRIVILEGES | MS_TOKEN_QUERY, &token) != 0 
	{
		luid: MS_LUID
		@static se_lock_memory_name := []u16{'S','e','L','o','c','k','M','e','m','o','r','y','P','r','i','v','i','l','e','g','e',0}
		if LookupPrivilegeValueW(nil, raw_data(se_lock_memory_name), &luid) != 0
		{
			priv := MS_TOKEN_PRIVILEGES {
				privilege_count = 1,
				privileges = {
					{
						luid = luid,
						attributes = MS_SE_PRIVILEGE_ENABLED,
					},
				},
			}
			AdjustTokenPrivileges(token, 0, &priv, size_of(MS_TOKEN_PRIVILEGES), nil, nil)
		}
		CloseHandle(token)
	}
}
os_init :: proc() {
	os_enable_large_pages()
	info                 := &os_windows_info.system_info
	info.target_page_size = int(GetLargePageMinimum())
}
os_system_info :: proc() -> ^OS_SystemInfo {
	return &os_windows_info.system_info
}
os_vmem_commit :: proc(vm: rawptr, size: int, no_large_pages: b32 = false) -> b32 {
	// Large pages disabled for now (not failing gracefully in original C)
	result := VirtualAlloc(vm, uintptr(size), MS_MEM_COMMIT, MS_PAGE_READWRITE) != nil
	return b32(result)
}
os_vmem_reserve :: proc(size: int, base_addr: int = 0, no_large_pages: b32 = false) -> rawptr {
	result := VirtualAlloc(rawptr(uintptr(base_addr)), uintptr(size),
		MS_MEM_RESERVE,
		// MS_MEM_COMMIT
		// | (no_large_pages ? 0 : MS_MEM_LARGE_PAGES), // Large pages disabled
		MS_PAGE_READWRITE)
	return result
}
os_vmem_release :: proc(vm: rawptr, size: int) {
	VirtualFree(vm, 0, MS_MEM_RELEASE)
}
//endregion OS

//region VArena
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

varena_make :: proc(reserve_size := Mega * 64, commit_size := Mega * 64, base_addr: int = 0, flags: VArenaFlags = {}) -> ^VArena {
	reserve_size := reserve_size
	commit_size  := commit_size
	if reserve_size == 0 { reserve_size = 64 * Mega } // 64MB
	if commit_size  == 0 { commit_size  = 64 * Mega } // 64MB
	reserve_size_aligned := align_pow2(reserve_size, os_system_info().target_page_size)
	commit_size_aligned  := align_pow2(commit_size,  os_system_info().target_page_size)
	no_large_pages       := .No_Large_Pages in flags ? cast(b32) true : cast(b32) false
	base := os_vmem_reserve(reserve_size_aligned, base_addr, no_large_pages)
	assert(base != nil)
	os_vmem_commit(base, commit_size_aligned, no_large_pages)
	header_size := align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT)
	vm := transmute(^VArena) base
	vm^ = VArena {
		reserve_start = int(uintptr(base)) + header_size,
		reserve       = reserve_size_aligned,
		commit_size   = commit_size_aligned,
		committed     = commit_size_aligned,
		commit_used   = header_size,
		flags         = flags,
	}
	return vm
}
varena_push :: proc(va: ^VArena, $Type: typeid, amount: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []Type {
	assert(va != nil)
	assert(amount != 0)
	requested_size := amount * size_of(Type)
	aligned_size   := align_pow2(requested_size, alignment)
	current_offset := va.reserve_start + va.commit_used
	to_be_used     := va.commit_used   + aligned_size
	reserve_left   := va.reserve       - va.commit_used
	commit_left    := va.committed     - va.commit_used
	exhausted      := commit_left      < to_be_used
	assert(to_be_used < reserve_left)
	if exhausted
	{
		next_commit_size: int
		if reserve_left > 0 {
			next_commit_size = max(va.commit_size, to_be_used)
		} 
		else {
			next_commit_size = align_pow2(reserve_left, os_system_info().target_page_size)
		}
		if next_commit_size > 0
		{
			next_commit_start := rawptr(uintptr(va) + uintptr(va.committed))
			no_large_pages    := cast(b32) (.No_Large_Pages in va.flags ? true : false)
			commit_result     := os_vmem_commit(next_commit_start, next_commit_size, no_large_pages)
			if ! commit_result {
				return {}
			}
			va.committed += next_commit_size
		}
	}
	va.commit_used = to_be_used
	return slice(transmute([^]Type) uintptr(current_offset), amount)
}
varena_release :: proc(va: ^VArena) {
	os_vmem_release(va, va.reserve)
}
varena_rewind :: proc(va: ^VArena, save_point: AllocatorSP) {
	assert(va != nil)
	assert(save_point.type_sig == varena_allocator_proc)
	va.commit_used = max(save_point.slot, size_of(VArena))
}
varena_reset :: proc(va: ^VArena) {
	va.commit_used = size_of(VArena)
}
varena_shrink :: proc(va: ^VArena, old_allocation: []byte, requested_size: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []byte {
	assert(va != nil)
	current_offset := va.reserve_start    + va.commit_used
	shrink_amount  := len(old_allocation) - requested_size
	if shrink_amount < 0 {
		return old_allocation
	}
	assert(raw_data(old_allocation) == rawptr(uintptr(current_offset)))
	va.commit_used -= shrink_amount
	return old_allocation[:requested_size]
}
varena_save :: #force_inline proc "contextless" (va: ^VArena) -> AllocatorSP { return AllocatorSP { type_sig = varena_allocator_proc, slot = va.commit_used } }
varena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	vm := transmute(^VArena) input.data
	switch input.op 
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = to_bytes(varena_push(vm, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(output.allocation)
		}
		
	case .Free:
		// No-op for arena
		
	case .Reset:
		varena_reset(vm)
		
	case .Grow, .Grow_NoZero:
		grow_amount := input.requested_size - len(input.old_allocation)
		if grow_amount == 0 {
			output.allocation = input.old_allocation
			return
		}
		current_offset := vm.reserve_start + vm.commit_used
		assert(raw_data(input.old_allocation) == rawptr(uintptr(current_offset)))

		allocation := to_bytes(varena_push(vm, byte, grow_amount, input.alignment))
		assert(raw_data(allocation) != nil)

		output.allocation = slice(cursor(input.old_allocation), input.requested_size)
		if input.op == .Grow {
			zero(cursor(output.allocation)[len(input.old_allocation):], grow_amount)
		}
		
	case .Shrink:
		current_offset := vm.reserve_start + vm.commit_used
		shrink_amount  := len(input.old_allocation) - input.requested_size
		if shrink_amount < 0 {
			output.allocation = input.old_allocation
			return
		}
		assert(raw_data(input.old_allocation) == rawptr(uintptr(current_offset)))
		vm.commit_used -= shrink_amount
		output.allocation = input.old_allocation[:input.requested_size]
		
	case .Rewind:
		varena_rewind(vm, input.save_point)
		
	case .SavePoint:
		output.save_point = varena_save(vm)
		
	case .Query:
		output.features   = {.Alloc, .Grow, .Shrink, .Reset, .Rewind}
		output.max_alloc  = vm.reserve - vm.committed
		output.min_alloc  = 4 * Kilo
		output.left       = output.max_alloc
		output.save_point = varena_save(vm)
	}
}
varena_ainfo :: #force_inline proc "contextless" (arena : ^VArena) -> AllocatorInfo { return AllocatorInfo{varena_allocator_proc, arena} }
//endregion VArena

//region Arena (Chained Arena)
ArenaFlag :: enum u32 {
	No_Large_Pages,
	No_Chaining,
}
ArenaFlags :: bit_set[ArenaFlag; u32]
Arena :: struct {
	backing:  ^VArena,
	prev:     ^Arena,
	current:  ^Arena,
	base_pos: int,
	pos:      int,
	flags:    ArenaFlags,
}

arena_make :: proc(reserve_size := Mega * 64, commit_size := Mega * 64, base_addr: int = 0, flags: ArenaFlags = {}) -> ^Arena {
	header_size := align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT)
	current     := varena_make(reserve_size, commit_size, base_addr, transmute(VArenaFlags) flags)
	assert(current != nil)
	arena := varena_push(current, Arena, 1)
	assert(len(arena) > 0)
	arena[0] = Arena {
		backing  = current,
		prev     = nil,
		current  = & arena[0],
		base_pos = 0,
		pos      = header_size,
		flags    = flags,
	}
	return & arena[0]
}
arena_push :: proc(arena: ^Arena, $Type: typeid, amount: int, alignment: int = MEMORY_ALIGNMENT_DEFAULT) -> []Type {
	assert(arena != nil)
	active         := arena.current
	size_requested := amount * size_of(Type)
	size_aligned   := align_pow2(size_requested, alignment)
	pos_pre        := active.pos
	pos_pst        := pos_pre + size_aligned
	should_chain   := (.No_Chaining not_in arena.flags) && (active.backing.reserve < pos_pst)	
	if should_chain {
		new_arena := arena_make(active.backing.reserve, active.backing.commit_size, 0, transmute(ArenaFlags) active.backing.flags)
		new_arena.base_pos = active.base_pos + active.backing.reserve
		sll_stack_push_n(& arena.current, & new_arena, & new_arena.prev)
		new_arena.prev = active
		active = arena.current
	}
	result_ptr := transmute([^]byte) (uintptr(active) + uintptr(pos_pre))
	vresult    := varena_push(active.backing, byte, size_aligned, alignment)
	slice_assert(vresult)
	assert(raw_data(vresult) == result_ptr)
	active.pos = pos_pst
	return slice(result_ptr, amount)
}
arena_release :: proc(arena: ^Arena) {
	assert(arena != nil)
	curr := arena.current
	for curr != nil {
		prev := curr.prev
		varena_release(curr.backing)
		curr = prev
	}
}
arena_reset :: proc(arena: ^Arena) {
	arena_rewind(arena, AllocatorSP { type_sig = arena_allocator_proc, slot = 0 })
}
arena_rewind :: proc(arena: ^Arena, save_point: AllocatorSP) {
	assert(arena != nil)
	assert(save_point.type_sig == arena_allocator_proc)
	header_size := align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT)
	curr        := arena.current
	big_pos     := max(header_size, save_point.slot)
	// Release arenas that are beyond the save point
	for curr.base_pos >= big_pos {
		prev := curr.prev
		varena_release(curr.backing)
		curr = prev
	}
	arena.current = curr
	new_pos      := big_pos - curr.base_pos
	assert(new_pos <= curr.pos)
	curr.pos = new_pos
	varena_rewind(curr.backing, { type_sig = varena_allocator_proc, slot = curr.pos + size_of(VArena) })
}
arena_save :: #force_inline proc(arena: ^Arena) -> AllocatorSP { return { type_sig = arena_allocator_proc, slot = arena.base_pos + arena.current.pos } }
arena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	arena := transmute(^Arena) input.data
	switch input.op
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = slice_to_bytes(arena_push(arena, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(output.allocation)
		}
		
	case .Free:
		// No-op for arena
		
	case .Reset:
		arena_reset(arena)
		
	case .Grow, .Grow_NoZero:
		active := arena.current
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := end(input.old_allocation)
		arena_end := transmute([^]byte) (uintptr(active) + uintptr(active.pos))
		if alloc_end == arena_end
		{
			// Can grow in place
			grow_amount  := input.requested_size - len(input.old_allocation)
			aligned_grow := align_pow2(grow_amount, input.alignment)
			if active.pos + aligned_grow <= active.backing.reserve
			{
				vresult := varena_push(active.backing, byte, aligned_grow, input.alignment)
				if len(vresult) > 0 {
					active.pos += aligned_grow
					output.allocation       = slice(raw_data(input.old_allocation), input.requested_size)
					output.continuity_break = false
					if input.op == .Grow {
						zero(cursor(output.allocation)[len(input.old_allocation):], grow_amount)
					}
					break
				}
			}
		}
		// Can't grow in place, allocate new
		new_alloc := arena_push(arena, byte, input.requested_size, input.alignment)
		if len(new_alloc) == 0 {
			output.allocation = {}
			break
		}
		copy(new_alloc, input.old_allocation)
		if input.op == .Grow {
			zero(cursor(new_alloc)[len(input.old_allocation):], input.requested_size - len(input.old_allocation))
		}
		output.allocation       = new_alloc
		output.continuity_break = true
		
	case .Shrink:
		active := arena.current
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := end(input.old_allocation)
		arena_end := transmute([^]byte) (uintptr(active) + uintptr(active.pos))
		if alloc_end != arena_end {
			// Not at the end, can't shrink but return adjusted size
			output.allocation = input.old_allocation[:input.requested_size]
			break
		}
		// Calculate shrinkage
		aligned_original := align_pow2(len(input.old_allocation), MEMORY_ALIGNMENT_DEFAULT)
		aligned_new      := align_pow2(input.requested_size, input.alignment)
		pos_reduction    := aligned_original - aligned_new
		active.pos       -= pos_reduction
		varena_shrink(active.backing, input.old_allocation, input.requested_size, input.alignment)
		output.allocation = input.old_allocation[:input.requested_size]
		
	case .Rewind:
		arena_rewind(arena, input.save_point)
		
	case .SavePoint:
		output.save_point = arena_save(arena)
		
	case .Query:
		output.features   = {.Alloc, .Grow, .Shrink, .Reset, .Rewind}
		output.max_alloc  = arena.backing.reserve
		output.min_alloc  = 4 * Kilo
		output.left       = output.max_alloc - arena.backing.commit_used
		output.save_point = arena_save(arena)
	}
}
arena_ainfo :: #force_inline proc "contextless" (arena : ^Arena) -> AllocatorInfo { return AllocatorInfo{arena_allocator_proc, arena} }
//endregion Arena (Casey-Ryan Composite Arena)

//region Hashing
hash64_djb8 :: proc(hash: ^u64, bytes: []byte) {
	for elem in bytes {
		hash^ = ((hash^ << 8) + hash^) + u64(elem)
	}
}
//endregion Hashing

//region Key Table 1-Layer Linear (KT1L)
KT1L_Slot :: struct($Type: typeid) {
	key:   u64,
	value: Type,
}
KT1L_Meta :: struct {
	slot_size:       uintptr,
	kt_value_offset: uintptr,
	type_width:      uintptr,
	type:            typeid,
}
kt1l_populate_slice_a2_Slice_Byte :: proc(kt: ^[]byte, backing: AllocatorInfo, values: []byte, num_values: int, m: KT1L_Meta) {
	assert(kt != nil)
	if num_values == 0 { return }
	table_size_bytes := num_values * int(m.slot_size)
	kt^               = mem_alloc(backing, table_size_bytes)
	slice_assert(kt ^)
	kt_raw : SliceByte = transmute(SliceByte) kt^
	for id in 0 ..< cast(uintptr) num_values {
		slot_offset := id * m.slot_size                                     // slot id
		slot_cursor := kt_raw.data[slot_offset:]                            // slots[id]            type: KT1L_<Type>
		slot_key    := cast(^u64) slot_cursor                               // slots[id].key        type: U64
		slot_value  := slice(slot_cursor[m.kt_value_offset:], m.type_width) // slots[id].value      type: <Type>
		a2_offset   := id * m.type_width * 2                                // a2 entry id
		a2_cursor   := cursor(values)[a2_offset:]                           // a2_entries[id]       type: A2_<Type>
		a2_key      := (transmute(^[]byte) a2_cursor) ^                     // a2_entries[id].key   type: <Type>
		a2_value    := slice(a2_cursor[m.type_width:], m.type_width)        // a2_entries[id].value type: <Type>
		copy(slot_value, a2_value)                                          // slots[id].value = a2_entries[id].value
		slot_key^ = 0; hash64_djb8(slot_key, a2_key)                        // slots[id].key   = hash64_djb8(a2_entries[id].key)
	}
	kt_raw.len = num_values
}
kt1l_populate_slice_a2 :: proc($Type: typeid, kt: ^[]KT1L_Slot(Type), backing: AllocatorInfo, values: [][2]Type) {
	assert(kt != nil)
	values_bytes := slice(transmute([^]u8) raw_data(values), len(values) * size_of([2]Type))
	kt1l_populate_slice_a2_Slice_Byte(transmute(^[]byte) kt, backing, values_bytes, len(values), {
		slot_size       = size_of(KT1L_Slot(Type)),
		kt_value_offset = offset_of(KT1L_Slot(Type), value),
		type_width      = size_of(Type),
		type            = Type,
	})
}
//endregion Key Table 1-Layer Linear (KT1L)

//region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)
KT1CX_Slot :: struct($type: typeid) {
	value:    type,
	key:      u64,
	occupied: b32,
}
KT1CX_Cell :: struct($type: typeid, $depth: int) {
	slots: [depth]KT1CX_Slot(type),
	next:  ^KT1CX_Cell(type, depth),
}
KT1CX :: struct($cell: typeid / KT1CX_Cell($type, $depth)) {
	cell_pool: []cell,
	table:     []cell,
}
KT1CX_Byte_Slot :: struct {
	key:      u64,
	occupied: b32,
}
KT1CX_Byte_Cell :: struct {
	next: ^byte,
}
KT1CX_Byte :: struct {
	cell_pool: []byte,
	table:     []byte,
}
KT1CX_ByteMeta :: struct {
	slot_size:        int,
	slot_key_offset:  uintptr,
	cell_next_offset: uintptr,
	cell_depth:       int,
	cell_size:        int,
	type_width:       int,
	type:             typeid,
}
KT1CX_InfoMeta :: struct {
	cell_pool_size:   int,
	table_size:       int,
	slot_size:        int,
	slot_key_offset:  uintptr,
	cell_next_offset: uintptr,
	cell_depth:       int,
	cell_size:        int,
	type_width:       int,
	type:             typeid,
}
KT1CX_Info :: struct {
	backing_table: AllocatorInfo,
	backing_cells: AllocatorInfo,
}
kt1cx_init :: proc(info: KT1CX_Info, m: KT1CX_InfoMeta, result: ^KT1CX_Byte) {
	assert(result                       != nil)
	assert(info.backing_cells.procedure != nil)
	assert(info.backing_table.procedure != nil)
	assert(m.cell_depth     >  0)
	assert(m.cell_pool_size >= 4 * Kilo)
	assert(m.table_size     >= 4 * Kilo)
	assert(m.type_width     >  0)
	table_raw       := transmute(SliceByte) mem_alloc(info.backing_table, m.table_size * m.cell_size)
	slice_assert(transmute([]byte) table_raw)
	result.cell_pool = mem_alloc(info.backing_cells, m.cell_size * m.cell_pool_size)
	slice_assert(result.cell_pool)
	table_raw.len = m.table_size
	result.table  = transmute([]byte) table_raw
}
kt1cx_clear :: proc(kt: KT1CX_Byte, m: KT1CX_ByteMeta) {
	cell_cursor := cursor(kt.table)
	table_len   := len(kt.table) * m.cell_size
	for ; cell_cursor != end(kt.table); cell_cursor = cell_cursor[m.cell_size:] // for cell, cell_id in kt.table.cells
	{
		slots       := SliceByte { cell_cursor, m.cell_depth * m.slot_size } // slots = cell.slots
		slot_cursor := slots.data
		for;; {
			slot := slice(slot_cursor, m.slot_size)          // slot = slots[slot_id]
			zero(slot)                                       // slot = {}
			if slot_cursor == end(transmute([]byte) slots) { // if slot == end(slot)
				next := slot_cursor[m.cell_next_offset:]       // next = kt.table.cells[cell_id + 1]
				if next != nil {                               // if next != nil
					slots.data  = next                           // slots = next.slots
					slot_cursor = next
					continue
				}
			}
			slot_cursor = slot_cursor[m.slot_size:]          // slot = slots[slot_id + 1]
		}
	}
}
kt1cx_slot_id :: proc(kt: KT1CX_Byte, key: u64, m: KT1CX_ByteMeta) -> u64 {
	cell_size := m.cell_size // dummy value
	hash_index := key % u64(len(kt.table))
	return hash_index
}
kt1cx_get :: proc(kt: KT1CX_Byte, key: u64, m: KT1CX_ByteMeta) -> ^byte {
	hash_index   := kt1cx_slot_id(kt, key, m)
	cell_offset  := uintptr(hash_index) * uintptr(m.cell_size)
	cell_cursor  := cursor(kt.table)[cell_offset:]                          // cell_id = 0
	{
		slots       := slice(cell_cursor, m.cell_depth * m.slot_size)         // slots   = cell[cell_id].slots
		slot_cursor := cell_cursor                                            // slot_id = 0
		for;; 
		{
			slot := transmute(^KT1CX_Byte_Slot) slot_cursor[m.slot_key_offset:] // slot = cell[slot_id]
			if slot.occupied && slot.key == key {
				return cast(^byte) slot_cursor
			}
			if slot_cursor == end(transmute([]byte) slots)
			{
				cell_next := cell_cursor[m.cell_next_offset:] // cell.next
				if cell_next != nil {
					slots       = slice(cell_next, len(slots)) // slots = cell.next
					slot_cursor = cell_next
					cell_cursor = cell_next                    // cell = cell.next
					continue
				}
				else {
					return nil
				}
			}
			slot_cursor = slot_cursor[m.slot_size:]
		}
	}
}
kt1cx_set :: proc(kt: KT1CX_Byte, key: u64, value: []byte, backing_cells: AllocatorInfo, m: KT1CX_ByteMeta) -> ^byte {
	hash_index  := kt1cx_slot_id(kt, key, m)
	cell_offset := uintptr(hash_index) * uintptr(m.cell_size)
	cell_cursor := cursor(kt.table)[cell_offset:] // KT1CX_Cell(Type) cell = kt.table[hash_index]
	{
		slots       := SliceByte {cell_cursor, m.cell_depth * m.slot_size} // cell.slots
		slot_cursor := slots.data
		for ;;
		{
			slot := transmute(^KT1CX_Byte_Slot) slot_cursor[m.slot_key_offset:]
			if slot.occupied == false {
				slot.occupied = true
				slot.key      = key
				return cast(^byte) slot_cursor
			}
			else if slot.key == key {
				return cast(^byte) slot_cursor
			}
			if slot_cursor == end(transmute([]byte) slots) {
				curr_cell := transmute(^KT1CX_Byte_Cell) (uintptr(cell_cursor) + m.cell_next_offset) // curr_cell = cell
				if curr_cell != nil {
					slots.data  = curr_cell.next
					slot_cursor = curr_cell.next
					cell_cursor = curr_cell.next
					continue
				}
				else {
					new_cell       := mem_alloc(backing_cells, m.cell_size)
					curr_cell.next  = raw_data(new_cell)
					slot            = transmute(^KT1CX_Byte_Slot) cursor(new_cell)[m.slot_key_offset:]
					slot.occupied   = true
					slot.key        = key
					return raw_data(new_cell)
				}
			}
			slot_cursor = slot_cursor[m.slot_size:]
		}
		return nil
	}
}
kt1cx_assert :: proc(kt: $type / KT1CX) {
	slice_assert(kt.cell_pool)
	slice_assert(kt.table)
}
kt1cx_byte :: proc(kt: $type / KT1CX) -> KT1CX_Byte { return { slice_to_bytes(kt.cell_pool), slice( transmute([^]byte) cursor(kt.table), len(kt.table)) } }
//endregion Key Table 1-Layer Chained-Chunked-Cells (KT1CX)

//region String Operations
char_is_upper :: proc(c: u8) -> b32 { return('A' <= c && c <= 'Z') }
char_to_lower :: proc(c: u8) -> u8  { c:=c; if (char_is_upper(c)) { c += ('a' - 'A') }; return (c) }

integer_symbols :: proc(value: u8) -> u8 {
	@static lookup_table: [16]u8 = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F', }; 
	return  lookup_table[value]; 
}

str8_to_cstr_capped :: proc(content: string, mem: []byte) -> cstring {
	copy_len := min(len(content), len(mem) - 1)
	if copy_len > 0 {
		copy(mem[:copy_len], transmute([]byte) content)
	}
	mem[copy_len] = 0
	return transmute(cstring) raw_data(mem)
}
str8_from_u32 :: proc(ainfo: AllocatorInfo, num: u32, radix: u32 = 10, min_digits: u8 = 0, digit_group_separator: u8 = 0) -> string {
	prefix: string
	switch radix {
	case 16: prefix = "0x"
	case 8:  prefix = "0o"
	case 2:  prefix = "0b"
	}
	digit_group_size: u32 = 3
	switch radix {
	case 2, 8, 16:
		digit_group_size = 4
	}
	needed_digits: u32 = 1
	if num > 0 
	{
		needed_digits = 0
		temp_num     := num
		for temp_num > 0 {
			temp_num /= radix
			needed_digits += 1
		}
	}
	needed_leading_zeros: u32
	if u32(min_digits) > needed_digits {
		needed_leading_zeros = u32(min_digits) - needed_digits
	}
	total_digits := needed_digits + needed_leading_zeros
	needed_separators: u32
	if digit_group_separator != 0 && total_digits > digit_group_size {
		needed_separators = (total_digits - 1) / digit_group_size
	}
	total_len    := len(prefix) + int(total_digits + needed_separators)
	result_bytes := mem_alloc(ainfo, total_len)
	if len(result_bytes) == 0 { return "" }
	result := transmute(string) result_bytes
	if len(prefix) > 0 {
		copy(result, prefix)
	}
	// Fill content from right to left
	write_cursor := total_len - 1
	num_reduce   := num
	for idx in 0..<total_digits 
	{
		if idx > 0 && idx % digit_group_size == 0 && digit_group_separator != 0 {
			result_bytes[write_cursor] = digit_group_separator
			write_cursor -= 1
		}
		
		if idx < needed_digits {
			result_bytes[write_cursor] = char_to_lower(integer_symbols(u8(num_reduce % radix)))
			num_reduce                /= radix
		} 
		else {
			result_bytes[write_cursor] = '0'
		}
		write_cursor -= 1
	}
	return result
}

str8_fmt_kt1l :: proc(ainfo: AllocatorInfo, _buffer: ^[]byte, table: []KT1L_Slot(string), fmt_template: string) -> string {
	buffer := _buffer^
	slice_assert(buffer)
	slice_assert(table)
	string_assert(fmt_template)
	if ainfo.procedure != nil {
		assert(.Grow in allocator_query(ainfo).features)
	}
	cursor_buffer    := cursor(buffer)
	buffer_remaining := len(buffer)

	curr_code  := fmt_template[0]
	cursor_fmt := cursor(transmute([]u8) fmt_template)
	left_fmt   := len(fmt_template)
	for ; left_fmt > 0 && buffer_remaining > 0;
	{
		// Forward until we hit the delimiter '<' or the template's contents are exhausted.
		for ; curr_code != '<' && cursor_fmt != end(fmt_template); {
			cursor_buffer[0]  = cursor_fmt   [0]
			cursor_buffer     = cursor_buffer[1:]
			cursor_fmt        = cursor_fmt   [1:]
			curr_code         = cursor_fmt   [0]
			buffer_remaining -= 1
			left_fmt         -= 1
		}
		if curr_code == '<'
		{
			cursor_potential_token := cursor_fmt[1:]
			potential_token_length := 0
			fmt_overflow           := b32(false)
			for ;; {
				cursor      := cursor_potential_token[potential_token_length:]
				fmt_overflow = cursor >= end(fmt_template)
				found_terminator := cast(b32) (cursor_potential_token[potential_token_length] == '>')
				if fmt_overflow || found_terminator do break
				potential_token_length += 1
			}
			if fmt_overflow do continue
			// Hashing the potential token and cross checking it with our token table
			key   : u64     = 0; hash64_djb8(& key, slice(cursor_potential_token, potential_token_length))
			value : ^string = nil
			for & token in table 
			{
				// We do a linear iteration instead of a hash table lookup because the user should be never substiuting with more than 100 unqiue tokens..
				if (token.key == key) {
					value = & token.value
					break
				}
			}
			if value != nil 
			{
				// We're going to appending the string, make sure we have enough space in our buffer.
				if ainfo.procedure != nil && (buffer_remaining - potential_token_length) <= 0 {
					buffer            = mem_grow(ainfo, buffer, len(buffer) + potential_token_length)
					buffer_remaining += potential_token_length
				}
				left         := len(value)
				cursor_value := cursor(transmute([]u8) value^)
				for ; left > 0 && buffer_remaining > 0; {
					cursor_buffer[0]  = cursor_value [0]
					cursor_buffer     = cursor_buffer[1:]
					cursor_value      = cursor_value [1:]
					cursor_fmt        = cursor_fmt   [1:]
					buffer_remaining -= 1
					left             -= 1
				}
				// Sync cursor format to after the processed token
				cursor_fmt = cursor_potential_token[potential_token_length + 1:]
				curr_code  = cursor_fmt[0]
				left_fmt  -= potential_token_length + 2 // The 2 here are the '<' & '>' delimiters being omitted.
				continue
			}
			cursor_buffer[0]  = cursor_fmt   [0]
			cursor_buffer     = cursor_buffer[1:]
			cursor_fmt        = cursor_fmt   [1:]
			curr_code         = cursor_fmt   [0]
			buffer_remaining -= 1
			left_fmt         -= 1
		}
	}
	_buffer ^ = buffer
	result := transmute(string) slice(cursor(buffer), len(buffer) - buffer_remaining)
	return result
}

str8_fmt_backed :: proc(tbl_ainfo, buf_ainfo: AllocatorInfo, fmt_template: string, entries: [][2]string) -> string {
	kt: []KT1L_Slot(string); kt1l_populate_slice_a2(string, & kt, tbl_ainfo, entries)
	buf_size := Kilo * 64
	buffer   := mem_alloc(buf_ainfo, buf_size)
	result   := str8_fmt_kt1l(buf_ainfo, & buffer, kt, fmt_template)
	return result
}
str8_fmt_tmp :: proc(fmt_template: string, entries: [][2]string) -> string {
	@static tbl_mem: [Kilo * 32]byte; tbl_arena := farena_make(tbl_mem[:])
	@static buf_mem: [Kilo * 64]byte; buffer := buf_mem[:]
	kt: []KT1L_Slot(string); kt1l_populate_slice_a2(string, & kt, ainfo(& tbl_arena), entries)
	result := str8_fmt_kt1l({}, & buffer, kt, fmt_template)
	return result
}

Str8Cache_CELL_DEPTH :: 4

KT1CX_Slot_Str8 :: KT1CX_Slot(string)
KT1CX_Cell_Str8 :: KT1CX_Cell(string, Str8Cache_CELL_DEPTH)
KT1CX_Str8      :: KT1CX(KT1CX_Cell_Str8)
Str8Cache :: struct {
	str_reserve:  AllocatorInfo,
	cell_reserve: AllocatorInfo,
	tbl_backing:  AllocatorInfo,
	kt:           KT1CX_Str8,
}
str8cache_init :: proc(cache: ^Str8Cache, str_reserve, cell_reserve, tbl_backing: AllocatorInfo, cell_pool_size := Kilo, table_size := Kilo) {
	assert(cache != nil)
	assert(str_reserve.procedure  != nil)
	assert(cell_reserve.procedure != nil)
	assert(tbl_backing.procedure  != nil)
	cache.str_reserve  = str_reserve
	cache.cell_reserve = cell_reserve
	cache.tbl_backing  = tbl_backing
	info := KT1CX_Info {
		backing_cells = cell_reserve,
		backing_table = tbl_backing,
	}
	m := KT1CX_InfoMeta {
		cell_pool_size   = cell_pool_size,
		table_size       = table_size,
		slot_size        = size_of(KT1CX_Slot_Str8),
		slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		cell_depth       = Str8Cache_CELL_DEPTH,
		cell_size        = size_of(KT1CX_Cell_Str8),
		type_width       = size_of(string),
		type             = string
	}
	kt1cx_init(info, m, transmute(^KT1CX_Byte) & cache.kt)
	return
}
str8cache_make :: proc(str_reserve, cell_reserve, tbl_backing: AllocatorInfo, cell_pool_size, table_size: int) -> Str8Cache { 
	cache : Str8Cache; str8cache_init(& cache, str_reserve, cell_reserve, tbl_backing, cell_pool_size, table_size); return cache 
}
str8cache_clear :: proc(kt: KT1CX_Str8) {
	kt1cx_assert(kt)
	kt1cx_clear(kt1cx_byte(kt), {
		slot_size        = size_of(KT1CX_Slot_Str8),
		slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		cell_depth       = Str8Cache_CELL_DEPTH,
		cell_size        = size_of(KT1CX_Cell_Str8),
		type_width       = size_of(string),
		type             = string,
	})
}
str8cache_get :: proc(kt: KT1CX_Str8, key: u64) -> ^string {
	kt1cx_assert(kt)
	result := kt1cx_get(kt1cx_byte(kt), key, {
		slot_size        = size_of(KT1CX_Slot_Str8),
		slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		cell_depth       = Str8Cache_CELL_DEPTH,
		cell_size        = size_of(KT1CX_Cell_Str8),
		type_width       = size_of(string),
		type             = string,
	})
	return transmute(^string) result
}
str8cache_set :: proc(kt: KT1CX_Str8, key: u64, value: string, str_reserve, cell_reserve: AllocatorInfo) -> ^string {
	kt1cx_assert(kt)
	slice_assert(transmute([]byte) value)
	assert(str_reserve.procedure  != nil)
	assert(cell_reserve.procedure != nil)
	entry := kt1cx_set(kt1cx_byte(kt), key, transmute([]byte) value, cell_reserve, {
		slot_size        = size_of(KT1CX_Slot_Str8),
		slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		cell_depth       = Str8Cache_CELL_DEPTH,
		cell_size        = size_of(KT1CX_Cell_Str8),
		type_width       = size_of(string),
		type             = string,
	})
	assert(entry != nil)
	result := transmute(^string) entry
	is_empty := len(result) == 0
	if is_empty {
		result ^ = transmute(string) alloc_slice(str_reserve, []u8, len(value))
		copy(result ^, value)
	}
	return result
}
cache_str8 :: proc(cache: ^Str8Cache, str: string) -> string {
	assert(cache != nil)
	key: u64 = 0; hash64_djb8(& key, transmute([]byte) str)
	result  := str8cache_set(cache.kt, key, str, cache.str_reserve, cache.cell_reserve)
	return result ^
}

Str8Gen :: struct {
	backing:  AllocatorInfo,
	ptr:     [^]u8,
	len:        int,
	cap:        int,
}
str8gen_init :: proc(gen: ^Str8Gen, ainfo: AllocatorInfo) {
	assert(gen != nil)
	gen.backing = ainfo
	gen.ptr     = raw_data(mem_alloc(ainfo, Kilo * 4))
	assert(gen.ptr != nil)
	gen.len = 0
	gen.cap = Kilo * 4
}
str8gen_make :: proc(ainfo: AllocatorInfo) -> Str8Gen { gen: Str8Gen; str8gen_init(& gen, ainfo); return gen }
str8gen_to_bytes  :: proc(gen: Str8Gen) -> []byte { return transmute([]byte) SliceByte {data = gen.ptr, len = gen.cap} }
str8_from_str8gen :: proc(gen: Str8Gen) -> string { return transmute(string) SliceByte {data = gen.ptr, len = gen.len} }

str8gen_append_str8 :: proc(gen: ^Str8Gen, str: string) {
	result := mem_grow(gen.backing, str8gen_to_bytes(gen ^), len(str) + gen.len)
	slice_assert(result)
	to_copy := slice(cursor(result)[gen.len:], len(result) - gen.len)
	copy(to_copy, transmute([]byte) str)
	gen.ptr = transmute(^u8) raw_data(result)
	gen.len = len(result)
	gen.cap = max(gen.len, gen.cap) // TODO(Ed): Arenas currently hide total capacity before growth. Problably better todo classic append to actually track this.
}
str8gen_append_fmt :: proc(gen: ^Str8Gen, fmt_template: string, tokens: [][2]string) {
	@static tbl_mem: [Kilo * 32]byte; tbl_arena := farena_make(tbl_mem[:])
	kt: []KT1L_Slot(string); kt1l_populate_slice_a2(string, & kt, ainfo(& tbl_arena), tokens)
	buffer := slice(gen.ptr[gen.len:], gen.cap - gen.len)
	if len(buffer) < Kilo * 16 {
		result := mem_grow(gen.backing, str8gen_to_bytes(gen ^), Kilo * 16 + gen.cap)
		slice_assert(result)
		gen.ptr  = raw_data(result)
		gen.cap += Kilo * 16
		buffer   = slice(gen.ptr[gen.len:], gen.cap - gen.len)
	}
	result := str8_fmt_kt1l(gen.backing, & buffer, kt, fmt_template)
	gen.len += len(result)
}
//#endregion String Operations

//region File System

// #include <fileapi.h>
MS_CREATE_ALWAYS         :: 2
MS_OPEN_EXISTING         :: 3
MS_GENERIC_READ          :: (0x80000000)
MS_GENERIC_WRITE         :: (0x40000000)
MS_FILE_SHARE_READ       :: 0x00000001
MS_FILE_SHARE_WRITE      :: 0x00000002
MS_FILE_ATTRIBUTE_NORMAL :: 0x00000080
MS_INVALID_FILE_SIZE     :: MS_DWORD(0xFFFFFFFF)
foreign kernel32 {
	CreateFileA :: proc(
		lpFileName:            MS_LPCSTR,
		dwDesiredAccess:       MS_DWORD,
		dwSharedMode:          MS_DWORD,
		lpSecurityAttributes:  MS_LPSECURITY_ATTRIBUTES,
		dwCreationDisposition: MS_DWORD,
		dwFlagsAndAttributes:  MS_DWORD,
		hTemplateFile:         MS_HANDLE,
	) -> MS_HANDLE ---
	ReadFile :: proc(
		hFile:                MS_HANDLE,
		lpBuffer:             MS_LPVOID,
		nNumberOfBytesToRead: MS_DWORD,
		lpNumberOfBytesRead:  MS_LPDWORD,
		lpOverlapped:         MS_LPOVERLAPPED,
	) -> MS_BOOL ---
	WriteFile :: proc(
		hFile:                  MS_HANDLE,
		lpBuffer:               MS_LPVOID,
		nNumberOfBytesToWrite:  MS_DWORD,
		lpNumberOfBytesWritten: MS_LPDWORD,
		lpOverlapped:           MS_LPOVERLAPPED,
	) -> MS_BOOL ---
	GetFileSizeEx :: proc(hFile: MS_HANDLE, lpFileSize: ^MS_LARGE_INTEGER) -> MS_BOOL ---
	GetLastError :: proc() -> MS_DWORD ---
}

FileOpInfo :: struct {
	content: []byte,
}
api_file_read_contents :: proc(result: ^FileOpInfo, path: string, backing: AllocatorInfo, zero_backing: b32 = false) {
	assert(result != nil)
	string_assert(path)
	assert(backing.procedure != nil)
	@static scratch: [Kilo * 64]u8
	path_cstr := str8_to_cstr_capped(path, scratch[:])
	id_file := CreateFileA(
		path_cstr,
		MS_GENERIC_READ,
		MS_FILE_SHARE_READ,
		nil,
		MS_OPEN_EXISTING,
		MS_FILE_ATTRIBUTE_NORMAL,
		nil
	)
	open_failed := uintptr(id_file) == MS_INVALID_HANDLE_VALUE
	if open_failed {
		error_code := GetLastError()
		assert(error_code != 0)
		return
	}
	file_size : MS_LARGE_INTEGER = { QuadPart = 0}
	get_size_failed := cast(MS_DWORD) ~ GetFileSizeEx(id_file, & file_size)
	if get_size_failed == MS_INVALID_FILE_SIZE {
		assert(get_size_failed == MS_INVALID_FILE_SIZE)
		return
	}
	buffer := mem_alloc(backing, cast(int) file_size.QuadPart)
	not_enough_backing := len(buffer) < cast(int) file_size.QuadPart
	if not_enough_backing {
		assert(not_enough_backing)
		result^ = {}
		return
	}
	if zero_backing {
		zero(buffer)
	}
	amount_read : MS_DWORD = 0
	read_result := ReadFile(
		id_file,
		raw_data(buffer),
		cast(MS_DWORD) file_size.QuadPart,
		& amount_read,
		nil
	)
	CloseHandle(id_file)
	read_failed := ! bool(read_result)
	read_failed |= amount_read != cast(u32) file_size.QuadPart
	if read_failed {
		assert(read_failed)
		return
	}
	result.content = slice(cursor(buffer), cast(int) file_size.QuadPart)
	return
}
file_read_contents_stack :: proc(path: string, backing: AllocatorInfo, zero_backing: b32 = false) -> FileOpInfo {
	result : FileOpInfo; api_file_read_contents(& result, path, backing, zero_backing)
	return result
}
file_write_str8 :: proc(path, content: string) {
	string_assert(path)
	@static scratch: [Kilo * 64]u8;
	path_cstr := str8_to_cstr_capped(path, scratch[:])
	id_file := CreateFileA(
		path_cstr,
		MS_GENERIC_WRITE,
		MS_FILE_SHARE_READ,
		nil,
		MS_CREATE_ALWAYS,
		MS_FILE_ATTRIBUTE_NORMAL,
		nil
	)
	open_failed := uintptr(id_file) == MS_INVALID_HANDLE_VALUE
	if open_failed {
		error_code := GetLastError()
		assert(error_code != 0)
		return
	}
	bytes_written : MS_DWORD = 0
	status := WriteFile(
		id_file,
		raw_data(content),
		cast(MS_DWORD) len(content),
		& bytes_written,
		nil
	)
	assert(status != 0)
	assert(bytes_written == cast(u32) len(content))
}
//endregion File System

//region WATL
WATL_TokKind :: enum u32 {
	Space           = ' ',
	Tab             = '\t',
	Carriage_Return = '\r',
	Line_Feed       = '\n',
	Text            = 0xFFFFFFFF,
}
WATL_Tok :: string
WATL_LexStatus_Flag :: enum u32 {
	MemFail_SliceConstraintFail,
}
WATL_LexStatus :: bit_set[WATL_LexStatus_Flag; u32]
WATL_Pos :: struct {
	line, column: i32,
}
WATL_LexMsg :: struct {
	next:    ^WATL_LexMsg,
	content:  string,
	tok:     ^WATL_Tok,
	pos:      WATL_Pos,
}
WATL_LexInfo :: struct {
	msgs:    ^WATL_LexMsg,
	toks:   []WATL_Tok,
	signal:   WATL_LexStatus,
}
api_watl_lex :: proc(info: ^WATL_LexInfo, source: string, 
	ainfo_msgs:                    AllocatorInfo, 
	ainfo_toks:                    AllocatorInfo, 
	failon_unsupported_codepoints: b8 = false, 
	failon_pos_untrackable:        b8 = false,
	failon_slice_constraint_fail : b8 = false,
) 
{
	if len(source) == 0 do return
	assert(info != nil)
	assert(ainfo_msgs.procedure != nil)
	assert(ainfo_toks.procedure != nil)
	msg_last : ^WATL_LexMsg

	src_cursor := cursor(source)
	end        := src_cursor[len(source):]
	prev       := src_cursor[-1:]
	code       := src_cursor[0]
	tok : ^Raw_String
	num : i32 = 0
	was_formatting := true
	for ; src_cursor < end;
	{
		alloc_tok :: #force_inline proc(ainfo: AllocatorInfo) -> ^Raw_String { 
			return alloc_type(ainfo, Raw_String, align_of(Raw_String), true) 
		}
		#partial switch cast(WATL_TokKind) code
		{
			case .Space: fallthrough
			case .Tab: 
				if prev[0] != src_cursor[0] {
					new_tok       := alloc_tok(ainfo_toks); if cursor(new_tok)[-1:] != tok && tok != nil { 
						slice_constraint_fail(info, ainfo_msgs, new_tok, & msg_last); 
						return 
					}
					tok            = new_tok
					tok^           = transmute(Raw_String) slice(src_cursor, 0)
					was_formatting = true
					num           += 1
				}
				src_cursor = src_cursor[1:]
				tok.len   += 1
			case .Line_Feed:
				new_tok       := alloc_tok(ainfo_toks); if cursor(new_tok)[-1:] != tok && tok != nil{ 
					slice_constraint_fail(info, ainfo_msgs, new_tok, & msg_last);
					return 
				}
				tok            = new_tok
				tok^           = transmute(Raw_String) slice(src_cursor, 1)
				src_cursor     = src_cursor[1:]
				was_formatting = true
				num           += 1
			case .Carriage_Return:
				new_tok       := alloc_tok(ainfo_toks); if cursor(new_tok)[-1:] != tok && tok != nil {
					slice_constraint_fail(info, ainfo_msgs, new_tok, & msg_last); 
					return
				}
				tok            = new_tok
				tok^           = transmute(Raw_String) slice(src_cursor, 2)
				src_cursor     = src_cursor[1:]
				was_formatting = true
				num           += 1
			case:
				if (was_formatting) {
					new_tok       := alloc_tok(ainfo_toks); if cursor(new_tok)[-1:] != tok && tok != nil {
						slice_constraint_fail(info, ainfo_msgs, new_tok, & msg_last);
						return
					}
					tok            = new_tok
					tok^           = transmute(Raw_String) slice(src_cursor, 0)
					was_formatting = false;
					num           += 1
				}
				src_cursor  = src_cursor[1:]
				tok.len    += 1
		}
		prev = src_cursor[-1:]
		code = src_cursor[0]
	}
	assert(tok != nil)
	assert(num > 0)
	info.toks = transmute([]string) slice(cursor(tok)[- num + 1:], num)
	return
	slice_constraint_fail :: proc(info: ^WATL_LexInfo, ainfo_msgs: AllocatorInfo, tok: ^Raw_String, msg_last: ^^WATL_LexMsg) {
		info.signal |= { .MemFail_SliceConstraintFail }
		msg         := alloc_type(ainfo_msgs, WATL_LexMsg)
		assert(msg != nil)
		msg.pos     = { -1, -1 }
		msg.tok     = transmute(^WATL_Tok) tok
		msg.content = "Token slice allocation was not contiguous"
		sll_queue_push_n(& info.msgs, msg_last, & msg)
		return
	}
}
watl_lex_stack :: #force_inline proc(source: string,
	ainfo_msgs:                    AllocatorInfo, 
	ainfo_toks:                    AllocatorInfo, 
	failon_unsupported_codepoints: b8 = false, 
	failon_pos_untrackable:        b8 = false,
	failon_slice_constraint_fail : b8 = false,
) -> (info: WATL_LexInfo)
{
	api_watl_lex(& info, 
		source, 
		ainfo_msgs,
		ainfo_toks,
		failon_unsupported_codepoints,
		failon_slice_constraint_fail,
		failon_pos_untrackable)
	return
}
WATL_Node :: string
WATL_Line :: []WATL_Node
WATL_ParseMsg :: struct {
	next:    ^WATL_ParseMsg,
	content:  string,
	line:    ^WATL_Line,
	tok:     ^WATL_Tok,
	pos:      WATL_Pos,
}
WATL_ParseStatus_Flag :: enum u32 {
	MemFail_SliceConstraintFail,
}
WATL_ParseStatus :: bit_set[WATL_ParseStatus_Flag; u32]
WATL_ParseInfo :: struct {
	lines: []WATL_Line,
	msgs:   ^WATL_ParseMsg,
	signal:  WATL_LexStatus,
}
api_watl_parse :: proc(info: ^WATL_ParseInfo, tokens: []WATL_Tok, 
	ainfo_msgs:  AllocatorInfo,
	ainfo_nodes: AllocatorInfo,
	ainfo_lines: AllocatorInfo,
	str_cache:   ^Str8Cache,
	failon_slice_constraint_fail: b32 = false,
)
{
	if len(tokens) == 0 do return
	assert(ainfo_lines.procedure != nil)
	assert(ainfo_msgs.procedure  != nil)
	assert(ainfo_nodes.procedure != nil)
	assert(str_cache             != nil)
	msg_last: ^WATL_ParseMsg

	info_lines := transmute(^SliceRaw(WATL_Node)) & info.lines
	line := alloc_type(ainfo_lines, SliceRaw(WATL_Node))
	curr := alloc_type(ainfo_nodes, WATL_Node)
	line ^       = { transmute([^]WATL_Node) curr, 0 }
	info_lines ^ = { transmute([^]WATL_Node) line, 0 }
	for & token in tokens
	{
		#partial switch cast(WATL_TokKind) token[0]
		{
			case .Carriage_Return: fallthrough
			case .Line_Feed:
				new_line := alloc_type(ainfo_lines, WATL_Line); if cursor(new_line)[-1:] != transmute(^[]string)line {
					info.signal |= { .MemFail_SliceConstraintFail }
					msg := alloc_type(ainfo_msgs, WATL_ParseMsg)
					msg.content = "Line slice allocation was not contiguous"
					msg.pos     = { cast(i32) len(info.lines), cast(i32) line.len }
					msg.line    = transmute(^[]WATL_Node) line
					msg.tok     = & token
					sll_queue_push_n(& info.msgs, & msg_last, & msg)
					assert(failon_slice_constraint_fail == false)
					return
				}
				line            = transmute(^SliceRaw(WATL_Node)) new_line
				line.data       = curr
				info_lines.len += 1
				continue

			case:
			break;
		}
		curr ^ = cache_str8(str_cache, token)
		new_node := alloc_type(ainfo_nodes, WATL_Node); if cursor(new_node)[-1:] != curr {
			info.signal |= { .MemFail_SliceConstraintFail }
			msg := alloc_type(ainfo_msgs, WATL_ParseMsg)
			msg.content = "Nodes slice allocation was not contiguous"
			msg.pos     = { cast(i32) len(info.lines), cast(i32) line.len }
			msg.line    = transmute(^[]WATL_Node) line
			msg.tok     = & token
			sll_queue_push_n(& info.msgs, & msg_last, & msg)
			return
		}
		curr = new_node
		line.len += 1
		continue
	}
}
watl_parse_stack :: #force_inline proc(tokens: []WATL_Tok, 
	ainfo_msgs:  AllocatorInfo,
	ainfo_nodes: AllocatorInfo,
	ainfo_lines: AllocatorInfo,
	str_cache:   ^Str8Cache,
	failon_slice_constraint_fail: b32 = false,
) -> (info: WATL_ParseInfo) 
{
	api_watl_parse(& info, 
		tokens,
		ainfo_msgs,
		ainfo_nodes,
		ainfo_lines,
		str_cache,
		failon_slice_constraint_fail)
	return
}
watl_dump_listing :: proc(buffer: AllocatorInfo, lines: []WATL_Line) -> string {
	@static scratch : [Kilo * 64]byte; sarena := farena_make(scratch[:]); sinfo := ainfo(& sarena)

	result := str8gen_make(buffer)
	line_num : u32 = 0
	for line in lines
	{
		str8gen_append_fmt(& result, "Line <line_num> - Chunks <chunk_num>:\n", {
			{ "line_num",  str8_from_u32(sinfo,            line_num, 10, 0, 0) },
			{ "chunk_num", str8_from_u32(sinfo, cast(u32) len(line), 10, 0, 0) }
		})
		for chunk in line 
		{
			id : string
			#partial switch cast(WATL_TokKind) chunk[0]
			{
				case .Space: id = "Space"
				case .Tab:   id = "Tab"
				case:        id = "Visible"
			}
			str8gen_append_fmt(& result, "\t<id>(<size>): '<chunk>'\n", {
				{ "id",    id },
				{ "size",  str8_from_u32(sinfo, cast(u32) len(chunk), 10, 0, 0) },
				{ "chunk", chunk }
			})
		}
		farena_reset(& sarena)
	}
	return str8_from_str8gen(result)
}
//endregion WATL

main :: proc()
{
	os_init()

	// Note(Ed): Possible compiler bug, cannot resolve proc map with named arguments.
	
	vm_file := varena_make(reserve_size = Giga * 4, flags = { .No_Large_Pages })
	// file    := file_read_contents("watl.v0.win32.odin", backing = ainfo(vm_file))
	file    := file_read_contents("watl.v0.win32.odin", ainfo(vm_file))
	slice_assert(file.content)

	a_msgs  := arena_make()
	a_toks  := arena_make()
	// lex_res := watl_lex(transmute(string) file.content, 
	// 	ainfo_msgs = ainfo(a_msgs), 
	// 	ainfo_toks = ainfo(a_toks),
	// )
	lex_res := watl_lex(transmute(string) file.content, 
		ainfo(a_msgs), 
		ainfo(a_toks),
	)
	assert(lex_res.signal & { .MemFail_SliceConstraintFail } == {})

	str8_cache_kt1_ainfo := arena_make()
	str_cache := str8cache_make(
		str_reserve    = ainfo(arena_make()),
		cell_reserve   = ainfo(str8_cache_kt1_ainfo),
		tbl_backing    = ainfo(str8_cache_kt1_ainfo),
		cell_pool_size = Kilo * 4,
		table_size     = Kilo * 32,
	)

	a_lines := arena_make()
	// parse_res := watl_parse(lex_res.toks,
	// 	ainfo_msgs  = ainfo(a_msgs),
	// 	ainfo_nodes = ainfo(a_toks),
	// 	ainfo_lines = ainfo(a_lines),
	// 	str_cache   = & str_cache
	// )
	parse_res := watl_parse(lex_res.toks,
		ainfo(a_msgs),
		ainfo(a_toks),
		ainfo(a_lines),
		& str_cache
	)
	assert(parse_res.signal & { .MemFail_SliceConstraintFail } == {})

	arena_reset(a_msgs)
	arena_reset(a_toks)
	listing := watl_dump_listing(ainfo(a_msgs), parse_res.lines)
	file_write_str8("watl.v0.win32.odin.listing.txt", listing)
	return
}

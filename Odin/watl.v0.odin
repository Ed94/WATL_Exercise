/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, WinAPI Only, Win CRT Multi-threaded Static Linkage)
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
end :: proc {
	slice_end,
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
zero :: proc {
	memory_zero,
	slice_zero,
}
zero_explicit :: proc {
	memory_zero_explicit,
}

watl_lex :: proc {
	api_watl_lex,
	watl_lex_stack,
}
watl_parse :: proc {
	api_watl_parse,
	watl_parse_stack,
}
//#endregion("Package Mappings")

//#region("Memory")
Kilo :: 1024
Mega :: Kilo * 1024
Giga :: Mega * 1024
Tera :: Giga * 1024

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
slice_assert :: proc (s: $SliceType / []$Type) {
	assert(len(s) > 0)
	assert(s != nil)
}
slice_end :: proc "contextless" (s : $SliceType / []$Type) -> ^Type {
	return & s[len(s) - 1]
}
@(require_results)
slice_to_bytes :: proc "contextless" (s: []$Type) -> []byte {
	return ([^]byte)(raw_data(s))[:len(s) * size_of(Type)]
}
slice_zero :: proc "contextless" (data: $SliceType / []$Type) {
	zero(raw_data(data), size_of(Type) * len(data))
}
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
sll_queue_push_nz :: proc(nil_val: ^$Type, first, last, n: ^^Type) {
	if (first ^) == nil_val {
		(first ^) = n
		(last  ^) = n
		n.next = nil_val
	}
	else {
		(last ^).next = n
		(last ^)      = n
		n.next        = nil_val
	}
}
sll_queue_push_n :: proc "contextless" (first: ^$Type, last, n: ^^Type) {
    sll_queue_push_nz(nil, first, last, n)
}
//#endregion("Memory")

//#region("Allocator Interface")
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
alloc_slice :: proc(ainfo: AllocatorInfo, $SliceType: []$Type, num : int) -> []Type {
	assert(ainfo.procedure != nil)
	input := AllocatorProc_In {
		data           = ainfo.data,
		op             = no_zero ? .Alloc_NoZero : .Alloc,
		requested_size = size_of(Type) * num,
		alignment      = alignment,
	}
	output: AllocatorProc_Out
	ainfo.procedure(input, & output)
	return transmute([]Type) Raw_Slice { raw_data(output.allocation), num }
}
//#endregion("Allocator Interface")

//#region("Strings")
Raw_String :: struct {
	data: [^]byte,
	len:     int,
}
string_copy   :: proc(dst, src: string) { slice_copy  (transmute([]byte) dst, transmute([]byte) src) }
string_assert :: proc(s: string)        { slice_assert(transmute([]byte) s) }
//#endregion("Strings")

//#region("FArena")
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
	ptr        := raw_data(arena.mem[arena.used:])
	arena.used += to_commit
	return transmute([]Type) Raw_Slice { data = ptr, len = amount }
}
farena_reset :: proc(arena: ^FArena) {
	arena.used = 0
}
farena_rewind :: proc(arena: ^FArena, save_point: AllocatorSP) {
	assert(save_point.type_sig  == farena_allocator_proc)
	assert(save_point.slot >= 0 && save_point.slot <= arena.used)
	arena.used = save_point.slot
}
farena_save :: proc(arena: FArena) -> AllocatorSP {
	return AllocatorSP { type_sig = farena_allocator_proc, slot = arena.used }
}
farena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	arena := cast(^FArena) input.data
	
	switch input.op 
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = slice_to_bytes(farena_push(arena, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(raw_data(output.allocation), len(output.allocation))
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
		alloc_end := uintptr(raw_data(input.old_allocation)) + uintptr(len(input.old_allocation))
		arena_end := uintptr(raw_data(arena.mem)) + uintptr(arena.used)
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
		output.allocation = transmute([]byte) Raw_Slice { 
			data = raw_data(input.old_allocation), 
			len  = input.requested_size 
		}
		if input.op == .Grow {
			zero(raw_data(output.allocation[len(input.old_allocation):]), grow_amount)
		}
		
	case .Shrink:
		// Check if the allocation is at the end of the arena
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := uintptr(raw_data(input.old_allocation)) + uintptr(len(input.old_allocation))
		arena_end := uintptr(raw_data(arena.mem))            + uintptr(arena.used)
		if alloc_end != arena_end {
			// Not at the end, can't shrink but return adjusted size
			output.allocation = transmute([]byte) Raw_Slice { 
				data = raw_data(input.old_allocation), 
				len  = input.requested_size 
			}
			break
		}
		// Calculate shrinkage
		aligned_original := align_pow2(len(input.old_allocation), MEMORY_ALIGNMENT_DEFAULT)
		aligned_new      := align_pow2(input.requested_size, input.alignment)
		arena.used       -= (aligned_original - aligned_new)
		output.allocation = transmute([]byte) Raw_Slice { 
			data = raw_data(input.old_allocation), 
			len  = input.requested_size 
		}
		
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
//#endregion("FArena")

//#region("OS")
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
MS_BOOL                :: i32
MS_DWORD               :: u32
MS_HANDLE              :: rawptr
MS_LPVOID              :: rawptr
MS_LPWSTR              :: [^]u16
MS_LUID                :: struct { low_part: MS_DWORD, high_part: i32 }
MS_LUID_AND_ATTRIBUTES :: struct { luid: MS_LUID, attributes: MS_DWORD }
MS_TOKEN_PRIVILEGES    :: struct { privilege_count: MS_DWORD, privileges: [1]MS_LUID_AND_ATTRIBUTES }
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
		MS_MEM_RESERVE | MS_MEM_COMMIT,
		// | (no_large_pages ? 0 : MS_MEM_LARGE_PAGES), // Large pages disabled
		MS_PAGE_READWRITE)
	return result
}
os_vmem_release :: proc(vm: rawptr, size: int) {
	VirtualFree(vm, 0, MS_MEM_RELEASE)
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

varena_make :: proc(reserve_size, commit_size: int, base_addr: int = 0, flags: VArenaFlags = {}) -> ^VArena {
	reserve_size := reserve_size
	commit_size  := commit_size
	if reserve_size == 0 { reserve_size = 64 * Mega } // 64MB
	if commit_size  == 0 { commit_size  = 64 * Mega } // 64MB
	reserve_size_aligned := align_pow2(reserve_size, os_system_info().target_page_size)
	commit_size_aligned  := align_pow2(commit_size, os_system_info().target_page_size)
	no_large_pages       := .No_Large_Pages in flags ? cast(b32) true : cast(b32) false
	base := os_vmem_reserve(reserve_size_aligned, base_addr, no_large_pages)
	assert(base != nil)
	os_vmem_commit(base, commit_size_aligned, no_large_pages)
	header_size := align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT)
	vm := cast(^VArena) base
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
	return transmute([]Type) Raw_Slice { 
		data = rawptr(uintptr(current_offset)), 
		len  = amount 
	}
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
	current_offset := va.reserve_start + va.commit_used
	shrink_amount  := len(old_allocation) - requested_size
	if shrink_amount < 0 {
		return old_allocation
	}
	assert(raw_data(old_allocation) == rawptr(uintptr(current_offset)))
	va.commit_used -= shrink_amount
	return transmute([]byte) Raw_Slice { 
		data = raw_data(old_allocation), 
		len  = requested_size 
	}
}
varena_save :: proc(va: ^VArena) -> AllocatorSP {
	return AllocatorSP { type_sig = varena_allocator_proc, slot = va.commit_used }
}
varena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	vm := cast(^VArena) input.data
	switch input.op 
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = slice_to_bytes(varena_push(vm, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(raw_data(output.allocation), len(output.allocation))
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

		allocation := slice_to_bytes(varena_push(vm, byte, grow_amount, input.alignment))
		assert(raw_data(allocation) != nil)

		output.allocation = transmute([]byte) Raw_Slice { 
			data = raw_data(input.old_allocation), 
			len = input.requested_size 
		}
		if input.op == .Grow {
			zero(raw_data(output.allocation[len(input.old_allocation):]), grow_amount)
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
		output.allocation = transmute([]byte) Raw_Slice { 
			data = raw_data(input.old_allocation), 
			len  = input.requested_size 
		}
		
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
//#endregion("VArena")

//#region("Arena (Casey-Ryan Composite Arena)")
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

arena_make :: proc(reserve_size, commit_size: int, base_addr: int = 0, flags: ArenaFlags = {}) -> ^Arena {
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
	result_ptr := rawptr(uintptr(active) + uintptr(pos_pre))
	vresult    := varena_push(active.backing, byte, size_aligned, alignment)
	slice_assert(vresult)
	assert(raw_data(vresult) == result_ptr)
	active.pos = pos_pst
	return transmute([]Type) Raw_Slice { data = result_ptr, len = amount }
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
arena_save :: proc(arena: ^Arena) -> AllocatorSP {
	return { type_sig = arena_allocator_proc, slot = arena.base_pos + arena.current.pos }
}
arena_allocator_proc :: proc(input: AllocatorProc_In, output: ^AllocatorProc_Out) {
	assert(output     != nil)
	assert(input.data != nil)
	arena := cast(^Arena) input.data
	switch input.op
	{
	case .Alloc, .Alloc_NoZero:
		output.allocation = slice_to_bytes(arena_push(arena, byte, input.requested_size, input.alignment))
		if input.op == .Alloc {
			zero(raw_data(output.allocation), len(output.allocation))
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
		alloc_end := uintptr(raw_data(input.old_allocation)) + uintptr(len(input.old_allocation))
		arena_end := uintptr(active) + uintptr(active.pos)
		if alloc_end == arena_end
		{
			// Can grow in place
			grow_amount := input.requested_size - len(input.old_allocation)
			aligned_grow := align_pow2(grow_amount, input.alignment)
			if active.pos + aligned_grow <= active.backing.reserve
			{
				vresult := varena_push(active.backing, byte, aligned_grow, input.alignment)
				if len(vresult) > 0 {
					active.pos += aligned_grow
					output.allocation = transmute([]byte) Raw_Slice {
						data = raw_data(input.old_allocation),
						len = input.requested_size,
					}
					output.continuity_break = false
					if input.op == .Grow {
						zero(raw_data(output.allocation[len(input.old_allocation):]), grow_amount)
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
			zero(raw_data(new_alloc[len(input.old_allocation):]), input.requested_size - len(input.old_allocation))
		}
		output.allocation = slice_to_bytes(new_alloc)
		output.continuity_break = true
		
	case .Shrink:
		active := arena.current
		if len(input.old_allocation) == 0 {
			output.allocation = {}
			break
		}
		alloc_end := uintptr(raw_data(input.old_allocation)) + uintptr(len(input.old_allocation))
		arena_end := uintptr(active) + uintptr(active.pos)
		if alloc_end != arena_end {
			// Not at the end, can't shrink but return adjusted size
			output.allocation = transmute([]byte) Raw_Slice {
				data = raw_data(input.old_allocation),
				len = input.requested_size,
			}
			break
		}
		// Calculate shrinkage
		aligned_original := align_pow2(len(input.old_allocation), MEMORY_ALIGNMENT_DEFAULT)
		aligned_new      := align_pow2(input.requested_size, input.alignment)
		pos_reduction    := aligned_original - aligned_new
		active.pos       -= pos_reduction
		varena_shrink(active.backing, input.old_allocation, input.requested_size, input.alignment)
		output.allocation = transmute([]byte) Raw_Slice {
			data = raw_data(input.old_allocation),
			len  = input.requested_size,
		}
		
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
//#endregion("Arena (Casey-Ryan Composite Arena)")

//#region("Hashing")
hash64_djb8 :: proc(hash: ^u64, bytes: []byte) {
	for elem in bytes {
		// This hash is a 1:1 translation of the C version's hash.
		hash^ = ((hash^ << 8) + hash^) + u64(elem)
	}
}
//#endregion("Hashing")

//#region("Key Table 1-Layer Linear (KT1L)")
KT1L_Slot :: struct($Type: typeid) {
	key:   u64,
	value: Type,
}
KT1L_Meta :: struct {
	slot_size:       uintptr,
	kt_value_offset: uintptr,
	type_width:      uintptr,
	type_name:       string,
}
kt1l_populate_slice_a2_Slice_Byte :: proc(kt: ^[]byte, backing: AllocatorInfo, values: []byte, num_values: int, m: KT1L_Meta) {
	assert(kt != nil)
	if num_values == 0 { return }
	table_size_bytes := num_values * int(m.slot_size)
	kt^               = mem_alloc(backing, table_size_bytes)
	slice_assert(kt ^)
	kt_raw : Raw_Slice = transmute(Raw_Slice) kt^
	for cursor in 0 ..< cast(uintptr) num_values {
		slot_offset := cursor * m.slot_size
		slot_cursor := uintptr(kt_raw.data) + slot_offset
		slot_key    := cast(^u64) slot_cursor
		slot_value  := transmute([]byte) Raw_Slice { cast([^]byte) (slot_cursor + m.kt_value_offset), int(m.type_width)}
		a2_offset   := cursor * m.type_width * 2
		a2_cursor   := uintptr(& values[a2_offset])
		a2_key      := (transmute(^[]byte) a2_cursor) ^
		a2_value    := transmute([]byte) Raw_Slice { rawptr(a2_cursor + m.type_width), int(m.type_width) }
		copy(slot_value, a2_value)
		slot_key^ = 0; hash64_djb8(slot_key, a2_key)
	}
	kt_raw.len = num_values
}
kt1l_populate_slice_a2 :: proc($Type: typeid, kt: ^[]KT1L_Slot(Type), backing: AllocatorInfo, values: [][2]Type) {
	assert(kt != nil)
	values_bytes := transmute([]byte) Raw_Slice{data = raw_data(values), len = len(values) * size_of([2]Type)}
	kt1l_populate_slice_a2_Slice_Byte(transmute(^[]byte) kt, backing, values_bytes, len(values), {
		slot_size       = size_of(KT1L_Slot(Type)),
		kt_value_offset = offset_of(KT1L_Slot(Type), KT1L_Slot(Type).value),
		type_width      = size_of(Type),
		type_name       = #type_string(Type),
	})
}
//#endregion("Key Table 1-Layer Linear (KT1L)")

//#region("Key Table 1-Layer Chained-Chunked-Cells (KT1CX)")
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
	type_name:        string,
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
	type_name:        string,
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
	table_raw       := transmute(Raw_Slice) mem_alloc(info.backing_table, m.table_size * m.cell_size)
	result.cell_pool = mem_alloc(info.backing_cells, m.cell_pool_size * m.cell_size)
	slice_assert(result.cell_pool)
	table_raw.len = m.table_size
	result.table  = transmute([]byte) table_raw
	slice_assert(result.table)
}
kt1cx_clear :: proc(kt: KT1CX_Byte, m: KT1CX_ByteMeta) {
	cursor    := cast(uintptr) raw_data(kt.table)
	num_cells := len(kt.table)
	table_len := len(kt.table) * m.cell_size
	for ; cursor != cast(uintptr) end(kt.table); cursor += cast(uintptr) m.cell_size
	{
		cell        := Raw_Slice { rawptr(cursor), m.cell_size }
		slots       := Raw_Slice { cell.data,      m.cell_depth * m.slot_size }
		slot_cursor := uintptr(slots.data)
		for;; { defer{slot_cursor += uintptr(m.slot_size)} {
			slot := transmute([]byte) Raw_Slice { rawptr(slot_cursor), m.slot_size }
			zero(slot)
			if slot_cursor == cast(uintptr) end(transmute([]byte) slots) {
				next := cast(rawptr) (slot_cursor + uintptr(m.cell_next_offset))
				if next != nil {
					slots.data  = next
					slot_cursor = uintptr(next)
					continue
				}
			}
		}}
	}
}
kt1cx_slot_id :: proc(kt: KT1CX_Byte, key: u64, m: KT1CX_ByteMeta) -> u64 {
	hash_index := key % u64(len(kt.table))
	return hash_index
}
kt1cx_get :: proc(kt: KT1CX_Byte, key: u64, m: KT1CX_ByteMeta) -> ^byte {
	hash_index   := kt1cx_slot_id(kt, key, m)
	cell_offset  := uintptr(hash_index) * uintptr(m.cell_size)
	cell         := Raw_Slice {& kt.table[cell_offset], m.cell_size}
	{
		slots       := Raw_Slice {cell.data, m.cell_depth * m.slot_size}
		slot_cursor := uintptr(slots.data)
		for;; { defer{slot_cursor += uintptr(m.slot_size)} 
		{
			slot := transmute(^KT1CX_Byte_Slot) (slot_cursor + m.slot_key_offset)
			if slot.occupied && slot.key == key {
				return cast(^byte) slot_cursor
			}
			if slot_cursor == cast(uintptr) end(transmute([]byte) slots)
			{
				cell_next := cast(rawptr) (uintptr(cell.data) + m.cell_next_offset)
				if cell_next != nil {
					slots.data  = cell_next
					slot_cursor = uintptr(cell_next)
					cell.data   = cell_next
					continue
				}
				else {
					return nil
				}
			}
		}}
	}
}
kt1cx_set :: proc(kt: KT1CX_Byte, key: u64, value: []byte, backing_cells: AllocatorInfo, m: KT1CX_ByteMeta) -> ^byte {
	hash_index  := kt1cx_slot_id(kt, key, m)
	cell_offset := uintptr(hash_index) * uintptr(m.cell_size)
	cell        := Raw_Slice{& kt.table[cell_offset], m.cell_size}
	{
		slots       := Raw_Slice {cell.data, m.cell_depth * m.slot_size}
		slot_cursor := uintptr(slots.data)
		for ;; { defer{slot_cursor += uintptr(m.slot_size)} 
		{
			slot := transmute(^KT1CX_Byte_Slot) rawptr(slot_cursor + m.slot_key_offset)
			if slot.occupied == false {
				slot.occupied = true
				slot.key      = key
				return cast(^byte) slot_cursor
			}
			else if slot.key == key {
				return cast(^byte) slot_cursor
			}
			if slot_cursor == uintptr(end(transmute([]byte) slots)) {
				curr_cell := transmute(^KT1CX_Byte_Cell) (uintptr(cell.data) + m.cell_next_offset)
				if curr_cell != nil {
					slots.data  = curr_cell.next
					slot_cursor = uintptr(curr_cell.next)
					cell.data   = curr_cell.next
					continue
				}
				else {
					new_cell       := mem_alloc(backing_cells, m.cell_size)
					curr_cell.next  = raw_data(new_cell)
					slot            = transmute(^KT1CX_Byte_Slot) rawptr(uintptr(raw_data(new_cell)) + m.slot_key_offset)
					slot.occupied   = true
					slot.key        = key
					return raw_data(new_cell)
				}
			}
		}}
		return nil
	}
}
kt1cx_assert :: proc(kt: $type / KT1CX) {
	slice_assert(kt.cell_pool)
	slice_assert(kt.table)
}
kt1cx_byte :: proc(kt: $type / KT1CX) -> KT1CX_Byte { return { slice_to_bytes(kt.cell_pool), slice_to_bytes(kt.table) } }
//#endregion("Key Table 1-Layer Chained-Chunked-Cells (KT1CX)")

//#region("String Operations")
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

str8_fmt_kt1l :: proc(ainfo: AllocatorInfo, buffer: []byte, table: []KT1L_Slot(string), fmt_template: string) -> string {
	slice_assert(buffer)
	slice_assert(table)
	string_assert(fmt_template)
	if ainfo.procedure != nil {
		assert(.Grow in allocator_query(ainfo).features)
	}
	cursor_buffer    := uintptr(raw_data(buffer))
	buffer_remaining := len(buffer)

	return {}
}

str8_fmt_backed :: proc(tbl_ainfo, buf_ainfo: AllocatorInfo, fmt_template: string, entries: [][2]string) -> string {
	return {}
}
str8_fmt_tmp :: proc(fmt_template: string, entries: [][2]string) -> string {
	return {}
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
str8cache_init :: proc(cache: ^Str8Cache, str_reserve, cell_reserve, tbl_backing: AllocatorInfo, cell_pool_size, table_size: int) {
}
str8cache_make :: proc(str_reserve, cell_reserve, tbl_backing: AllocatorInfo, cell_pool_size, table_size: int) -> Str8Cache { 
	cache : Str8Cache; str8cache_init(& cache, str_reserve, cell_reserve, tbl_backing, cell_pool_size, table_size); return cache 
}
str8cache_clear :: proc(kt: KT1CX_Str8) {
}
str8cache_get :: proc(kt: KT1CX_Str8, key: u64) -> ^string {
	return nil
}
str8cache_set :: proc(kt: KT1CX_Str8, key: u64, value: string, str_reserve, cell_reserve: AllocatorInfo) -> ^string {
	return nil
}
cache_str8 :: proc(cache: ^Str8Cache, str: string) -> ^string {
	 return nil
}

Str8Gen :: struct {
	backing:  AllocatorInfo,
	ptr:     ^u8,
	len:      int,
	cap:      int,
}
str8gen_init :: proc(gen: ^Str8Gen, ainfo: AllocatorInfo) {

}
str8gen_make :: proc(ainfo: AllocatorInfo) -> Str8Gen { gen: Str8Gen; str8gen_init(& gen, ainfo); return gen }
str8gen_to_bytes  :: proc(gen: Str8Gen) -> []byte { return transmute([]byte) Raw_Slice {data = gen.ptr, len = gen.len} }
str8_from_str8gen :: proc(gen: Str8Gen) -> string { return transmute(string) Raw_Slice {data = gen.ptr, len = gen.len} }

str8gen_append_str8 :: proc(gen: ^Str8Gen, str: string) {
}
str8gen_append_fmt :: proc(gen: ^Str8Gen, fmt_template: string, tokens: [][2]string) {
}
//#endregion("String Operations")

//#region("File System")
FileOpInfo :: struct {
	content: []byte,
}
api_file_read_contents :: proc(result: ^FileOpInfo, path: string, backing: AllocatorInfo, zero_backing: b32 = false) {
}
file_read_contents_stack :: proc(path: string, backing: AllocatorInfo, zero_backing: b32 = false) -> FileOpInfo {
	return {}
}
//#endregion("File System")

//#region("WATL")
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
) {
}
watl_lex_stack :: proc(source: string,
	ainfo_msgs:                    AllocatorInfo, 
	ainfo_toks:                    AllocatorInfo, 
	failon_unsupported_codepoints: b8 = false, 
	failon_pos_untrackable:        b8 = false,
	failon_slice_constraint_fail : b8 = false,
) -> (info: WATL_LexInfo)
{
	return
}
WATL_Node :: string
WATL_Line :: []WATL_Node
WATL_ParseMsg :: struct {
	next:    ^WATL_ParseMsg,
	content:  string,
	line:    ^WATL_Line,
	tok:     ^WATL_Tok,
	pos:     ^WATL_Pos,
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
	failon_slice_constraint_fail: b32,
) {
}
watl_parse_stack :: proc(tokens: []WATL_Tok, 
	ainfo_msgs:  AllocatorInfo,
	ainfo_nodes: AllocatorInfo,
	ainfo_lines: AllocatorInfo,
	str_cache:   ^Str8Cache,
	failon_slice_constraint_fail: b32,
) -> (info: WATL_ParseInfo) 
{
	return
}
//#endregion("WATL")

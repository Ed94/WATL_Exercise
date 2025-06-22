/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, MSVC & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: odin-lang/Odin dev-2025-06
*/
package odin

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
size_of_slice_type :: proc(slice: $Type / []$SliceType) -> int {
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

sll_stack_push_n :: proc(first: ^$SLL_NodeType, n: ^SLL_NodeType) {
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
sll_queue_push_n :: proc(first: ^$SLL_NodeType, last: ^SLL_NodeType, n: ^SLL_NodeType) {
    sll_queue_push_nz(nil, first, last, n)
}
//#endregion("Memory")

//#region("Strings")
Raw_String :: struct {
	data: [^]byte,
	len:  int,
}
//#endregion("Strings")

main :: proc()
{

}

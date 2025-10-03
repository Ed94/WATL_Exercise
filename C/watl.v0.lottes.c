/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, LLVM & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: LLVM (2025-08-30), C-Stanard: 11

Based on: Neokineogfx - Fixing C
https://youtu.be/RrL7121MOeA
*/

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-const-variable"
#pragma clang diagnostic ignored "-Wunused-but-set-variable"
#pragma clang diagnostic ignored "-Wswitch"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wunknown-pragmas"
#pragma clang diagnostic ignored "-Wvarargs"
#pragma clang diagnostic ignored "-Wunused-function"
#pragma clang diagnostic ignored "-Wbraced-scalar-init"
#pragma clang diagnostic ignored "-W#pragma-messages"
#pragma clang diagnostic ignored "-Wstatic-in-inline"
#pragma clang diagnostic ignored "-Wkeyword-macro"
#pragma clang diagnostic ignored "-Wc23-compat"
#pragma clang diagnostic ignored "-Wreserved-identifier"
#pragma clang diagnostic ignored "-Wpre-c11-compat"
#pragma clang diagnostic ignored "-Wc23-extensions"
#pragma clang diagnostic ignored "-Wunused-macros"
#pragma clang diagnostic ignored "-Wdeclaration-after-statement"
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"
#pragma clang diagnostic ignored "-Wc++-keyword"
#pragma clang diagnostic ignored "-Wimplicit-function-declaration"
#pragma clang diagnostic ignored "-Wcast-align"
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wswitch-default"
#pragma clang diagnostic ignored "-Wmissing-field-initializers"
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#pragma clang diagnostic ignored "-Wpointer-sign"

#pragma region Header

#pragma region DSL
#if 0
// Original macros

#define A_(x)   __attribute__((aligned (x)))
#define E_(x,y) __builtin_expect(x,y)
#define S_ static
#define I_ static inline __attribute__((always_inline))
#define N_ static        __attribute__((noinline))
#define R_            __restrict                                     
#define V_            volatile                                       
// #define W_            __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))
#endif

// Ones I'm deciding to use..

#define align_(value) __attribute__((aligned (value)))             // for easy alignment
#define expect_(x, y) __builtin_expect(x, y)                       // so compiler knows the common path
#define finline       static inline __attribute__((always_inline)) // force inline
#define noinline      static        __attribute__((noinline))      // force no inline [used in thread api]
#define R_            __restrict                                   // pointers are either restricted or volatile and nothing else 
#define V_            volatile                                     // pointers are either restricted or volatile and nothing else
// #define W_            __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))

#define glue_impl(A, B)    A ## B
#define glue(A, B)         glue_impl(A, B)
#define stringify_impl(S)  #S
#define stringify(S)       stringify_impl(S)
#define tmpl(prefix, type) prefix ## _ ## type

#define local_persist      static
#define global             static

#define static_assert      _Static_assert
#define typeof             __typeof__
#define typeof_ptr(ptr)    typeof(ptr[0])
#define typeof_same(a, b)  _Generic((a), typeof((b)): 1, default: 0)

#define def_R_(type)      type* restrict type ## _R
#define def_V_(type)      type* volatile type ## _V
#define def_ptr_set(type) def_R_(type); typedef def_V_(type)
#define def_tset(type) type; typedef def_ptr_set(type)

typedef __UINT8_TYPE__  def_tset(U1); typedef __UINT16_TYPE__ def_tset(U2); typedef __UINT32_TYPE__ def_tset(U4); typedef __UINT64_TYPE__ def_tset(U8);
typedef __INT8_TYPE__   def_tset(S1); typedef __INT16_TYPE__  def_tset(S2); typedef __INT32_TYPE__  def_tset(S4); typedef __INT64_TYPE__  def_tset(S8);
typedef unsigned char   def_tset(B1); typedef __UINT16_TYPE__ def_tset(B2); typedef __UINT32_TYPE__ def_tset(B4);
typedef float  def_tset(F4); 
typedef double def_tset(F8);
typedef float  V4_F4 __attribute__((vector_size(16))); typedef def_ptr_set(V4_F4);
enum { false = 0, true  = 1, true_overflow, };

#define u1_r(value) cast(U1_R, value)
#define u2_r(value) cast(U2_R, value)
#define u4_r(value) cast(U4_R, value)
#define u8_r(value) cast(U8_R, value)
#define u1_v(value) cast(U1_V, value)
#define u2_v(value) cast(U2_V, value)
#define u4_v(value) cast(U4_V, value)
#define u8_v(value) cast(U8_V, value)

#define u1_(value) cast(U1, value)
#define u2_(value) cast(U2, value)
#define u4_(value) cast(U4, value)
#define u8_(value) cast(U8, value)
#define s1_(value) cast(S1, value)
#define s2_(value) cast(S2, value)
#define s4_(value) cast(S4, value)
#define s8_(value) cast(S8, value)
#define f4_(value) cast(F4, value)
#define f8_(value) cast(F8, value)

#define farray_len(array)                   (SSIZE)sizeof(array) / size_of( typeof((array)[0]))
#define farray_init(type, ...)              (type[]){__VA_ARGS__}
#define def_farray_sym(_type, _len)         A ## _len ## _ ## _type
#define def_farray_impl(_type, _len)        _type def_farray_sym(_type, _len)[_len]; typedef def_ptr_set(def_farray_sym(_type, _len))
#define def_farray(type, len)               def_farray_impl(type, len)
#define def_enum(underlying_type, symbol)   underlying_type def_tset(symbol); enum   symbol
#define def_struct(symbol)                  struct symbol   def_tset(symbol); struct symbol
#define def_union(symbol)                   union  symbol   def_tset(symbol); union  symbol
#define def_proc(symbol)                    symbol
#define opt_args(symbol, ...)               &(symbol){__VA_ARGS__}

#define alignas                             _Alignas
#define alignof                             _Alignof
#define cast(type, data)                    ((type)(data))
#define pcast(type, data)                   * cast(type*, & (data))
#define nullptr                             cast(void*, 0)
#define null                                cast(U8,    0)
#define offset_of(type, member)             cast(U8, & (((type*) 0)->member))
#define size_of(data)                       cast(U8, sizeof(data))

#define kilo(n)                             (cast(U8, n) << 10)
#define mega(n)                             (cast(U8, n) << 20)
#define giga(n)                             (cast(U8, n) << 30)
#define tera(n)                             (cast(U8, n) << 40)

// Signed stuff (still diff flavor from Lottes)

#define sop_1(op, a, b) cast(U1, s1_(a) op s1_(b))
#define sop_2(op, a, b) cast(U2, s2_(a) op s2_(b))
#define sop_4(op, a, b) cast(U4, s4_(a) op s4_(b))
#define sop_8(op, a, b) cast(U8, s8_(a) op s8_(b))

#define def_signed_op(id, op, width) finline U ## width id ## _s ## width(U ## width a, U ## width b) {return sop_ ## width(op, a, b); }
#define def_signed_ops(id, op)       def_signed_op(id, op, 1) def_signed_op(id, op, 2) def_signed_op(id, op, 4) def_signed_op(id, op, 8)
def_signed_ops(add, +) def_signed_ops(sub, -) def_signed_ops(mut, *) def_signed_ops(div, /)
def_signed_ops(gt,  >) def_signed_ops(lt,  <) def_signed_ops(ge, >=) def_signed_ops(le, <=)

#define def_generic_sop(op, a, ...) _Generic((a), U1:  op ## _s1, U2: op ## _s2, U4: op ## _s4, U8: op ## _s8) (a, __VA_ARGS__)
#define add_s(a,b) def_generic_sop(add,a,b)
#define sub_s(a,b) def_generic_sop(sub,a,b)
#define mut_s(a,b) def_generic_sop(mut,a,b)
#define gt_s(a,b)  def_generic_sop(gt, a,b)
#define lt_s(a,b)  def_generic_sop(lt, a,b)
#define ge_s(a,b)  def_generic_sop(ge, a,b)
#define le_s(a,b)  def_generic_sop(le, a,b)

finline U4 AtmAdd_u4 (U4_R a, U4 v){__asm__ volatile("lock xaddl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U8 AtmAdd_u8 (U8_R a, U8 v){__asm__ volatile("lock xaddq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U4 AtmSwap_u4(U4_R a, U4 v){__asm__ volatile("lock xchgl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U8 AtmSwap_u8(U8_R a, U8 v){__asm__ volatile("lock xchgq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
#pragma endregion DSL

#pragma region Strings
typedef unsigned char def_tset(UTF8);
typedef def_struct(Str8) { UTF8*R_ ptr; U8 len; };
typedef Str8 def_tset(Slice_UTF8);
typedef def_struct(Slice_Str8) { Str8*R_ ptr; U8 len; };
#define lit(string_literal) (Str8){ (UTF8*R_) string_literal, size_of(string_literal) - 1 }
#pragma endregion Strings

#pragma region Debug
#define debug_trap()      __debugbreak()
#define assert_trap(cond) do { if (cond) __debug_trap(); } while(0)
#define assert_msg(cond, msg, ...) do { \
	if (! (cond))            \
	{                        \
		assert_handler(        \
			stringify(cond),     \
			__FILE__,            \
			__func__,            \
			cast(S4, __LINE__),  \
			msg,                 \
			## __VA_ARGS__);     \
		debug_trap();          \
	}                        \
} while(0)
void assert_handler(UTF8*R_ condition, UTF8*R_ file, UTF8*R_ function, S4 line, UTF8*R_ msg, ... );
#pragma endregion Debug

#pragma region Memory
typedef def_farray(B1, 1);
typedef def_farray(B1, 2);
typedef def_farray(B1, 4);
typedef def_farray(B1, 8);

inline U8 align_pow2(U8 x, U8 b);

#define align_struct(type_width) ((U8)(((type_width) + 7) / 8 * 8))

#define assert_bounds(point, start, end) do { \
	assert(start <= point); \
	assert(point <= end);   \
} while(0)

U8 mem_copy            (U8 dest, U8 src, U8 length);
U8 mem_copy_overlapping(U8 dest, U8 src, U8 length);
B4 mem_zero            (U8 dest, U8 length);
 
finline void BarC(void){__asm__ volatile("::""memory");} // Compiler Barrier
finline void BarM(void){__builtin_ia32_mfence();}        // Memory   Barrier
finline void BarR(void){__builtin_ia32_lfence();}        // Read     Barrier
finline void BarW(void){__builtin_ia32_sfence();}        // Write    Barrier

#define check_nil(nil, p) ((p) == 0 || (p) == nil)
#define set_nil(nil, p)   ((p) = nil)

#define sll_stack_push_n(f, n, next) do { (n)->next = (f); (f) = (n); } while(0)

#define sll_queue_push_nz(nil, f, l, n, next) \
(                           \
	check_nil(nil, f) ? (     \
		(f) = (l) = (n),        \
		set_nil(nil, (n)->next) \
	)                         \
	: (                       \
		(l)->next=(n),          \
		(l) = (n),              \
		set_nil(nil,(n)->next)  \
	)                         \
)
#define sll_queue_push_n(f, l, n, next) sll_queue_push_nz(0, f, l, n, next)

typedef def_struct(Slice_Mem) { U8 ptr; U8 len; };
#define slice_mem(ptr, len) (Slice_Mem){ptr, len}

#define def_Slice(type)           def_struct(tmpl(Slice,type)) { type*R_ ptr; U8 len; }; typedef def_ptr_set(tmpl(Slice,type))
#define slice_assert(slice)       do { assert((slice).ptr != 0); assert((slice).len > 0); } while(0)
#define slice_end(slice)          ((slice).ptr + (slice).len)
#define size_of_slice_type(slice) size_of( * (slice).ptr )

typedef def_Slice(void);
typedef def_Slice(B1);
#define slice_byte(slice) ((Slice_B1){cast(B1, (slice).ptr), (slice).len * size_of_slice_type(slice)})
#define slice_fmem(mem)   ((Slice_B1){ mem, size_of(mem) })

void slice__copy(Slice_B1 dest, U8 dest_typewidth, Slice_B1 src, U8 src_typewidth);
void slice__zero(Slice_B1 mem, U8 typewidth);
#define slice_copy(dest, src) do {       \
	static_assert(typeof_same(dest, src)); \
	slice__copy(slice_byte(dest),  size_of_slice_type(dest), slice_byte(src), size_of_slice_type(src)); \
} while (0)
#define slice_zero(slice) slice__zero(slice_byte(slice), size_of_slice_type(slice))

#define slice_iter(container, iter)     typeof((container).ptr) iter = (container).ptr; iter != slice_end(container); ++ iter
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) { .ptr = farray_init(type, __VA_ARGS__), .len = farray_len( farray_init(type, __VA_ARGS__)) }

#define span_iter(type, iter, m_begin, op, m_end)  \
	tmpl(Iter_Span,type) iter = { \
		.r = {(m_begin), (m_end)},   \
		.cursor = (m_begin) };       \
	iter.cursor op iter.r.end;     \
	++ iter.cursor

#define def_span(type)                                                \
	        def_struct(tmpl(     Span,type)) { type begin; type end; }; \
	typedef def_struct(tmpl(Iter_Span,type)) { tmpl(Span,type) r; type cursor; }

typedef def_span(B1);
typedef def_span(U4);
typedef def_span(U8);
#pragma endregion Memory

#pragma region Math
#define min(A, B)       (((A) < (B)) ? (A) : (B))
#define max(A, B)       (((A) > (B)) ? (A) : (B))
#define clamp_bot(X, B) max(X, B)
#pragma endregion Math

#pragma region Allocator Interface
typedef def_enum(U4, AllocatorOp) {
	AllocatorOp_Alloc_NoZero = 0, // If Alloc exist, so must No_Zero
	AllocatorOp_Alloc,
	AllocatorOp_Free,
	AllocatorOp_Reset,
	AllocatorOp_Grow_NoZero,
	AllocatorOp_Grow,
	AllocatorOp_Shrink,
	AllocatorOp_Rewind,
	AllocatorOp_SavePoint,
	AllocatorOp_Query, // Must always be implemented
};
typedef def_enum(U4, AllocatorQueryFlags) {
	AllocatorQuery_Alloc        = (1 << 0),
	AllocatorQuery_Free         = (1 << 1),
	// Wipe the allocator's state
	AllocatorQuery_Reset        = (1 << 2),
	// Supports both grow and shrink
	AllocatorQuery_Shrink       = (1 << 4),
	AllocatorQuery_Grow         = (1 << 5),
	AllocatorQuery_Resize       = AllocatorQuery_Grow | AllocatorQuery_Shrink,
	// Ability to rewind to a save point (ex: arenas, stack), must also be able to save such a point
	AllocatorQuery_Rewind       = (1 << 6),
};
typedef struct AllocatorProc_In  def_tset(AllocatorProc_In);
typedef struct AllocatorProc_Out def_tset(AllocatorProc_Out);
typedef struct AllocatorSP       AllocatorSP;
typedef void def_proc(AllocatorProc) (AllocatorProc_In In, AllocatorProc_Out_R Out);
struct AllocatorSP {
	AllocatorProc* type_sig;
	U8             slot;
};
struct AllocatorProc_In {
	U8 data;
	U8 requested_size;
	U8 alignment;
	union {
		Slice_Mem   old_allocation;
		AllocatorSP save_point;
	};
	AllocatorOp    op;
	A4_B1 _PAD_;
};
struct AllocatorProc_Out {
	union {
		Slice_Mem   allocation;
		AllocatorSP save_point;
	};
	AllocatorQueryFlags features;
	A4_B1 _PAD_;
	U8                  left; // Contiguous memory left
	U8                  max_alloc;
	U8                  min_alloc;
	B4                  continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
	A4_B1 _PAD_2;
};
typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	U8             data;
};
static_assert(size_of(AllocatorSP) <= size_of(Slice_Mem));
typedef def_struct(AllocatorQueryInfo) {
	AllocatorSP         save_point;
	AllocatorQueryFlags features;
	A4_B1 _PAD_;
	U8                  left; // Contiguous memory left
	U8                  max_alloc;
	U8                  min_alloc;
	B4                  continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
	A4_B1 _PAD_2;
};
static_assert(size_of(AllocatorProc_Out) == size_of(AllocatorQueryInfo));

#define MEMORY_ALIGNMENT_DEFAULT (2 * size_of(void*))

AllocatorQueryInfo allocator_query(AllocatorInfo ainfo);

void        mem_free      (AllocatorInfo ainfo, Slice_Mem mem);
void        mem_reset     (AllocatorInfo ainfo);
void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
AllocatorSP mem_save_point(AllocatorInfo ainfo);

typedef def_struct(Opts_mem_alloc)  { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_grow)   { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_shrink) { U8 alignment; };
typedef def_struct(Opts_mem_resize) { U8 alignment; B4 no_zero; A4_B1 _PAD_; };

Slice_Mem mem__alloc (AllocatorInfo ainfo,                U8 size, Opts_mem_alloc_R  opts);
Slice_Mem mem__grow  (AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow_R   opts);
Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize_R opts);
Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink_R opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, opt_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo,   mem, size, ...) mem__grow  (ainfo, mem, size, opt_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, opt_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, opt_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*R_)           mem__alloc(ainfo, size_of(type),        opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ mem__alloc(ainfo, size_of(type) * num,  opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
typedef def_struct(Opts_farena) {
	Str8 type_name;
	U8   alignment;
};
typedef def_struct(FArena) {
	U8 start;
	U8 capacity;
	U8 used;
};
typedef def_ptr_set(FArena);
FArena      farena_make  (Slice_Mem mem);
void        farena_init  (FArena_R arena, Slice_Mem byte);
Slice_Mem   farena__push (FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts);
void        farena_reset (FArena_R arena);
void        farena_rewind(FArena_R arena, AllocatorSP save_point);
AllocatorSP farena_save  (FArena  arena);

void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_farena(arena) (AllocatorInfo){ .proc = farena_allocator_proc, .data = & arena }

#define farena_push_mem(arena, amount, ...) farena__push(arena, amount, 1, opt_args(Opts_farena, lit(stringify(B1)), __VA_ARGS__))

#define farena_push(arena, type, ...) \
cast(type*, farena__push(arena, size_of(type), 1, opt_args(Opts_farena, lit(stringify(type)), __VA_ARGS__))).ptr

#define farena_push_array(arena, type, amount, ...) \
(Slice ## type){ farena__push(arena, size_of(type), amount, opt_args(Opts_farena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion FArena

#pragma region OS
finline U8   Clk  (void){U8 aa,dd;__asm__ volatile("rdtsc":"=a"(aa),"=d"(dd));return aa;}
finline void Pause(void){__asm__ volatile("pause":::"memory");}

typedef def_struct(OS_SystemInfo) {
	U8 target_page_size;
};
typedef def_struct(Opts_vmem) {
	U8    base_addr;
	B4    no_large_pages;
	A4_B1 _PAD_;
};
void os_init(void);
OS_SystemInfo* os_system_info(void);

inline B4    os__vmem_commit (U8 vm, U8 size, Opts_vmem*R_ opts);
inline U8    os__vmem_reserve(       U8 size, Opts_vmem*R_ opts);
inline void  os_vmem_release (U8 vm, U8 size);

#define os_vmem_reserve(size, ...)    os__vmem_reserve(    size, opt_args(Opts_vmem, __VA_ARGS__))
#define os_vmem_commit(vm, size, ...) os__vmem_commit (vm, size, opt_args(Opts_vmem, __VA_ARGS__))
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
typedef Opts_farena Opts_varena;
typedef def_enum(U4, VArenaFlags) {
	VArenaFlag_NoLargePages = (1 << 0),
};
typedef def_struct(VArena) {
	U8 reserve_start;
	U8 reserve;
	U8 commit_size;
	U8 committed;
	U8 commit_used;
	VArenaFlags flags;
	A4_B1 _PAD;
};
typedef def_struct(Opts_varena_make) {
	U8 base_addr;
	U8 reserve_size;
	U8 commit_size;
	VArenaFlags flags;
	A4_B1 _PAD_;
};
VArena_R varena__make(Opts_varena_make*R_ opts);
#define   varena_make(...) varena__make(opt_args(Opts_varena_make, __VA_ARGS__))

Slice_Mem   varena__push  (VArena_R arena, U8 amount, U8 type_width, Opts_varena*R_ opts);
void        varena_release(VArena_R arena);
void        varena_rewind (VArena_R arena, AllocatorSP save_point);
void        varena_reset  (VArena_R arena);
Slice_Mem   varena__shrink(VArena_R arena, Slice_Mem old_allocation, U8 requested_size, Opts_varena*R_ opts);
AllocatorSP varena_save   (VArena_R arena);

void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_varena(varena) (AllocatorInfo) { .proc = & varena_allocator_proc, .data = varena }

#define varena_push_mem(arena, amount, ...) varena__push(arena, amount, 1, opt_args(Opts_varena, lit(stringify(B1)), __VA_ARGS__))

#define varena_push(arena, type, ...) \
cast(type*R_, varena__push(arena, 1, size_of(type), opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define varena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ varena__push(arena, size_of(type), amount, opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion VArena

#pragma region Arena (Casey-Ryan Composite Arenas)
typedef Opts_varena Opts_arena;
typedef def_enum(U4, ArenaFlags) {
	ArenaFlag_NoLargePages = (1 << 0),
	ArenaFlag_NoChain      = (1 << 1),
};
typedef def_struct(Arena) {
	VArena_R   backing;
	Arena_R    prev;
	Arena_R    current;
	U8         base_pos;
	U8         pos;
	ArenaFlags flags;
	A4_B1 _PAD_;
};
typedef Opts_varena_make Opts_arena_make;
Arena_R     arena__make  (Opts_arena_make*R_ opts);
Slice_Mem   arena__push  (Arena_R arena, U8 amount, U8 type_width, Opts_arena*R_ opts);
void        arena_release(Arena_R arena);
void        arena_reset  (Arena_R arena);
void        arena_rewind (Arena_R arena, AllocatorSP save_point);
AllocatorSP arena_save   (Arena_R arena);

void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_arena(arena) (AllocatorInfo){ .proc = & arena_allocator_proc, .data = arena }

#define arena_make(...) arena__make(opt_args(Opts_arena_make, __VA_ARGS__))

#define arena_push_mem(arena, amount, ...) arena__push(arena, amount, 1, opt_args(Opts_arena, lit(stringify(B1)), __VA_ARGS__))

#define arena_push(arena, type, ...) \
cast(type*R_, arena__push(arena, 1, size_of(type), opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define arena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ arena__push(arena, size_of(type), amount, opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion Arena

#pragma region Hashing
finline
void hash64_djb8(U8_R hash, Slice_Mem bytes) {
	U8 elem = bytes.ptr;
loop:
	hash[0] <<= 8;
	hash[0]  += hash[0];
	hash[0]  += elem;
	if (elem != bytes.ptr + bytes.len) 
	goto end;
	++ elem;
	goto loop;
end:
	return;
}
#pragma endregion Hashing

#pragma region Key Table 1-Layer Linear (KT1L)
#define def_KT1L_Slot(type)        \
def_struct(tmpl(KT1L_Slot,type)) { \
	U8   key;   \
	type value; \
}
#define def_KT1L(type)             \
	def_Slice(tmpl(KT1L_Slot,type)); \
	typedef tmpl(Slice_KT1L_Slot,type) tmpl(KT1L,type)

typedef Slice_Mem KT1L_Byte;
typedef def_struct(KT1L_Meta) {
	U8 slot_size;
	U8 kt_value_offset;
	U8 type_width;
	Str8 type_name;
};
void kt1l__populate_slice_a2(KT1L_Byte*R_ kt, AllocatorInfo backing, KT1L_Meta m, Slice_Mem values, U8 num_values );
#define kt1l_populate_slice_a2(type, kt, ainfo, values) kt1l__populate_slice_a2(  \
	cast(KT1L_Byte*R_, kt),                                      \
	ainfo,                                                       \
	(KT1L_Meta){                                                 \
		.slot_size       = size_of(tmpl(KT1L_Slot,type)),          \
		.kt_value_offset = offset_of(tmpl(KT1L_Slot,type), value), \
		.type_width      = size_of(type),                          \
		.type_name       = lit(stringify(type))                    \
	},                                                           \
	slice_byte(values), (values).len                             \
)
#pragma endregion KT1L

#pragma region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)
#define def_KT1CX_Slot(type)        \
def_struct(tmpl(KT1CX_Slot,type)) { \
	type value;   \
	U8  key;      \
	B4  occupied; \
	A4_B1 _PAD_;  \
}
#define def_KT1CX_Cell(type, depth)      \
def_struct(tmpl(KT1CX_Cell,type)) {      \
	tmpl(KT1CX_Slot,type)    slots[depth]; \
	tmpl(KT1CX_Slot,type)*R_ next;         \
}
#define def_KT1CX(type)                  \
def_struct(tmpl(KT1CX,type)) {           \
	tmpl(Slice_KT1CX_Cell,type) cell_pool; \
	tmpl(Slice_KT1CX_Cell,type) table;     \
}
typedef def_struct(KT1CX_Byte_Slot) {
	U8   key;
	B4   occupied;
	A4_B1 _PAD_;
};
typedef def_struct(KT1CX_Byte_Cell) {
	U8 next;
};
typedef def_struct(KT1CX_Byte) {
	Slice_Mem cell_pool;
	Slice_Mem table;
};
typedef def_struct(KT1CX_ByteMeta) {
	U8   slot_size;
	U8   slot_key_offset;
	U8   cell_next_offset;
	U8   cell_depth;
	U8   cell_size;
	U8   type_width;
	Str8 type_name;
};
typedef def_struct(KT1CX_InfoMeta) {
	U8   cell_pool_size;
	U8   table_size;
	U8   slot_size;
	U8   slot_key_offset;
	U8   cell_next_offset;
	U8   cell_depth;
	U8   cell_size;
	U8   type_width;
	Str8 type_name;
};
typedef def_struct(KT1CX_Info) {
	AllocatorInfo backing_table;
	AllocatorInfo backing_cells;
};
void kt1cx_init   (KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte*R_ result);
void kt1cx_clear  (KT1CX_Byte kt,  KT1CX_ByteMeta meta);
U8   kt1cx_slot_id(KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
U8   kt1cx_get    (KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
U8   kt1cx_set    (KT1CX_Byte kt,  U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta);

#define kt1cx_assert(kt) do {   \
	slice_assert(kt.cell_pool); \
	slice_assert(kt.table);     \
} while(0)
#define kt1cx_byte(kt) (KT1CX_Byte){slice_byte(kt.cell_pool), { cast(U8, kt.table.ptr), kt.table.len } }
#pragma endregion KT1CX

#pragma region String Operations
finline B4 char_is_upper(U8 c) { return('A' <= c && c <= 'Z'); }
finline U8 char_to_lower(U8 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return(c); }
inline U8 integer_symbols(U8 value) {
	local_persist U1 lookup_table[16] = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F', }; return lookup_table[cast(U1, value)]; 
}

char* str8_to_cstr_capped(Str8 content, Slice_Mem mem);
Str8  str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U8 min_digits, U8 digit_group_separator);

typedef def_farray(Str8, 2);
typedef def_Slice(A2_Str8);
typedef def_KT1L_Slot(Str8);
typedef def_KT1L(Str8);

Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8* entries);
#define str8_fmt_backed(tbl_backing, buf_backing, fmt_template, ...) \
str8__fmt_backed(tbl_backing, buf_backing, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))

Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8*R_ entries);
#define str8_fmt(fmt_template, ...) str8__fmt(lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))

#define Str8Cache_CELL_DEPTH 4

typedef def_KT1CX_Slot(Str8);
typedef def_KT1CX_Cell(Str8, Str8Cache_CELL_DEPTH);
typedef def_Slice(KT1CX_Cell_Str8);
typedef def_KT1CX(Str8);
typedef def_struct(Str8Cache) {
	AllocatorInfo str_reserve;
	AllocatorInfo cell_reserve;
	AllocatorInfo tbl_backing;
	KT1CX_Str8    kt;
};

typedef def_struct(Opts_str8cache_init) {
	AllocatorInfo str_reserve;
	AllocatorInfo cell_reserve;
	AllocatorInfo tbl_backing;
	U8 cell_pool_size;
	U8 table_size;
};
void      str8cache__init(Str8Cache_R cache, Opts_str8cache_init*R_ opts);
Str8Cache str8cache__make(                   Opts_str8cache_init*R_ opts);

#define str8cache_init(cache, ...) str8cache__init(cache, opt_args(Opts_str8cache_init, __VA_ARGS__))
#define str8cache_make(...)        str8cache__make(       opt_args(Opts_str8cache_init, __VA_ARGS__))

void  str8cache_clear(KT1CX_Str8 kt);
U8 str8cache_get(KT1CX_Str8 kt, U8 key);
U8 str8cache_set(KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells);

Str8 cache_str8(Str8Cache* cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	U8 ptr;
	U8 len;
	U8 cap;
};
void    str8gen_init(Str8Gen_R gen, AllocatorInfo backing);
Str8Gen str8gen_make(               AllocatorInfo backing);

#define str8gen_slice_mem(gen) (Slice_mem){ cast(U8, (gen).ptr), (gen).cap }

finline Str8 str8_from_str8gen(Str8Gen gen) { return (Str8){ cast(UTF8_R, gen.ptr), gen.len}; }

void str8gen_append_str8(U8 gen, Str8 str);
void str8gen__append_fmt(U8 gen, Str8 fmt_template, Slice_A2_Str8*R_ tokens);

#define str8gen_append_fmt(gen, fmt_template, ...) str8gen__append_fmt(gen, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))
#pragma endregion String Operations

#pragma region File System
typedef def_struct(FileOpInfo) {
	Slice_Mem content;
};
typedef def_struct(Opts_read_file_contents) {
	AllocatorInfo backing;
	B4            zero_backing;
	A4_B1 _PAD_;
};
void api_file_read_contents(FileOpInfo*R_ result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents*R_ opts);
#define file_read_contents(path, ...) file__read_contents(path, &(Opts_read_file_contents){__VA_ARGS__})
#pragma endregion File System

#pragma region WATL
typedef def_enum(U4, WATL_TokKind) {
	WATL_Tok_Space          = ' ',
	WATL_Tok_Tab            = '\t',
	WATL_Tok_CarriageReturn = '\r',
	WATL_Tok_LineFeed       = '\n',
	WATL_Tok_Text           = 0xFFFFFFF,
};
typedef Str8 def_tset(WATL_Tok);
typedef def_Slice(WATL_Tok);
typedef def_enum(U4, WATL_LexStatus) {
	WATL_LexStatus_MemFail_SliceConstraintFail = (1 << 0),
};
typedef def_struct(WATL_Pos) {
	S4 line;
	S4 column;
};
typedef def_struct(WATL_LexMsg) {
	WATL_LexMsg_R next;
	Str8          content;
	WATL_Tok_R    tok;
	WATL_Pos      pos;
};
typedef def_struct(WATL_LexInfo) {
	WATL_LexMsg_R  msgs;
	Slice_WATL_Tok toks;
	WATL_LexStatus signal;
	A4_B1 _PAD_;
};
typedef def_struct(Opts_watl_lex) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_toks;
	B1 failon_unsupported_codepoints;
	B1 failon_pos_untrackable;
	B1 failon_slice_constraint_fail;
	A4_B1 _PAD_;
};
void         api_watl_lex(WATL_LexInfo* info, Str8 source, Opts_watl_lex*R_ opts);
WATL_LexInfo watl__lex   (                    Str8 source, Opts_watl_lex*R_ opts);
#define watl_lex(source, ...) watl__lex(source, &(Opts_watl_lex){__VA_ARGS__})

typedef Str8 WATL_Node;
typedef def_Slice(WATL_Node);
typedef Slice_WATL_Node def_tset(WATL_Line);
typedef def_Slice(WATL_Line);
typedef def_struct(WATL_ParseMsg) {
	WATL_ParseMsg_R next;
	Str8        content;
	WATL_Line_R line;
	WATL_Tok_R  tok;
	WATL_Pos    pos;
};
typedef def_enum(U4, WATL_ParseStatus) {
	WATL_ParseStatus_MemFail_SliceConstraintFail = (1 << 0),
};
typedef def_struct(WATL_ParseInfo) {
	Slice_WATL_Line  lines;
	WATL_ParseMsg_R  msgs;
	WATL_ParseStatus signal;
	A4_B1 _PAD_;
};
typedef def_struct(Opts_watl_parse) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_nodes;
	AllocatorInfo ainfo_lines;
	Str8Cache_R   str_cache;
	B4 failon_slice_constraint_fail;
	A4_B1 _PAD_;
};
void           api_watl_parse(WATL_ParseInfo_R info, Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
WATL_ParseInfo watl__parse   (                       Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
#define watl_parse(tokens, ...) watl__parse(tokens, &(Opts_watl_parse){__VA_ARGS__})

Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines);
#pragma endregion WATL

#pragma endregion Header

#pragma region Implementation

#pragma region Memory Operations
void* __cdecl memcpy (void*R_ _Dst, void const*R_ _Src, U8 _Size);
void* __cdecl memmove(void*   _Dst, void const*   _Src, U8 _Size);
void* __cdecl memset (void*R_ _Dst, int           _Val, U8 _Size);
inline
U8 align_pow2(U8 x, U8 b) {
    assert(b != 0);
    assert((b & (b - 1)) == 0);  // Check power of 2
    return ((x + b - 1) & (~(b - 1)));
}
U8 memory_copy(U8 dest, U8 src, U8 len) __asm__("memcpy");
U8 memory_copy_overlapping(U8 dest, U8 src, U8 len) __asm__("memmove");
inline
B4 memory_zero(U8 dest, U8 length) {
	if (dest == 0) return false;
	memset((void*R_)dest, 0, length);
	return true;
}
inline void slice__zero(Slice_B1 mem, U8 typewidth) { slice_assert(mem); memory_zero(u8_(mem.ptr), mem.len); }
inline
void slice__copy(Slice_B1 dest, U8 dest_typewidth, Slice_B1 src, U8 src_typewidth) {
	assert(dest.len >= src.len);
	slice_assert(dest);
	slice_assert(src);
	memory_copy(u8_(dest.ptr), u8_(src.ptr), src.len);
}
#pragma endregion Memory Operations

#pragma region Allocator Interface
inline
AllocatorQueryInfo allocator_query(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	AllocatorQueryInfo out; ainfo.proc((AllocatorProc_In){ .data = ainfo.data, .op = AllocatorOp_Query}, (AllocatorProc_Out_R)& out); 
	return out;
}
inline
void mem_free(AllocatorInfo ainfo, Slice_Mem mem) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Free, .old_allocation = mem}, &(AllocatorProc_Out){});
}
inline
void mem_reset(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Reset}, &(AllocatorProc_Out){});
}
inline
void mem_rewind(AllocatorInfo ainfo, AllocatorSP save_point) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Rewind, .save_point = save_point}, &(AllocatorProc_Out){});
}
inline
AllocatorSP mem_save_point(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	AllocatorProc_Out out;
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_SavePoint}, & out);
	return out.save_point;
}
inline
Slice_Mem mem__alloc(AllocatorInfo ainfo, U8 size, Opts_mem_alloc* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In  in = {
		.data           = ainfo.data,
		.op             = opts->no_zero ?  AllocatorOp_Alloc_NoZero : AllocatorOp_Alloc,
		.requested_size = size,
		.alignment      = opts->alignment,
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}
inline
Slice_Mem mem__grow(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = opts->no_zero ? AllocatorOp_Grow_NoZero : AllocatorOp_Grow,
		.requested_size = size,
		.alignment      = opts->alignment,
		.old_allocation = mem
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}
inline
Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = mem.len < size ? AllocatorOp_Shrink : (opts->no_zero ? AllocatorOp_Grow : AllocatorOp_Grow_NoZero),
		.requested_size = size,
		.alignment      = opts->alignment,
		.old_allocation = mem,
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}
inline
Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = AllocatorOp_Shrink,
		.requested_size = size,
		.alignment      = opts->alignment,
		.old_allocation = mem
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
inline
void farena_init(FArena* arena, Slice_Mem mem) {
	assert(arena != nullptr);
	arena->start    = mem.ptr;
	arena->capacity = mem.len;
	arena->used     = 0;
}
inline FArena farena_make(Slice_Mem mem) { FArena a; farena_init(& a, mem); return a; }
inline
Slice_Mem farena__push(FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts) {
	assert(opts != nullptr);
	if (amount == 0) {
		return (Slice_Mem){};
	}
	U8 desired   = type_width * amount;
	U8 to_commit = align_pow2(desired, opts->alignment ?  opts->alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 unused    = arena->capacity - arena->used;
	assert(to_commit <= unused);
	U8 ptr       = arena->start + arena->used;
	arena->used +=  to_commit;
	return (Slice_Mem){ptr, desired};
}
inline void farena_reset(FArena* arena) { arena->used = 0; }
inline
void farena_rewind(FArena_R arena, AllocatorSP save_point) {
	assert(save_point.type_sig == & farena_allocator_proc);
	U8 end = arena->start + arena->used;
	assert_bounds(save_point.slot, arena->start, end);
	arena->used -= save_point.slot - arena->start;
}
inline
AllocatorSP farena_save (FArena  arena) {
	AllocatorSP sp = { .type_sig = & farena_allocator_proc, .slot = arena.used };
	return sp;
}
void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	assert(out != nullptr);
	assert(in.data != 0);
	FArena* arena = cast(FArena*, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = farena_push_mem(arena, in.requested_size, .alignment = in.alignment);
			memory_zero(out->allocation.ptr, out->allocation.len * in.op);
		break;

		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			farena_reset(arena);
		break;

		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero: {
			// Check if the allocation is at the end of the arena
			U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
			U8 arena_end = arena->start + arena->used;
			if (alloc_end != arena_end) {
				// Not at the end, can't grow in place
				out->allocation = (Slice_Mem){0};
				break;
			}
			// Calculate growth
			U8 grow_amount  = in.requested_size - in.old_allocation.len;
			U8 aligned_grow = align_pow2(grow_amount, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
			U8 unused       = arena->capacity - arena->used;
			if (aligned_grow > unused) {
				// Not enough space
				out->allocation = (Slice_Mem){0};
				break;
			}
			arena->used += aligned_grow;
			out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
			memory_zero(in.old_allocation.ptr + in.old_allocation.len, grow_amount * in.op - AllocatorOp_Grow_NoZero);
		}
		break;

		case AllocatorOp_Shrink: {
			// Check if the allocation is at the end of the arena
			U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
			U8 arena_end = arena->start + arena->used;
			if (alloc_end != arena_end) {
				// Not at the end, can't shrink but return adjusted size
				out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
				break;
			}
			// Calculate shrinkage
			//SSIZE shrink_amount    = in.old_allocation.len - in.requested_size;
			U8 aligned_original = align_pow2(in.old_allocation.len, MEMORY_ALIGNMENT_DEFAULT);
			U8 aligned_new      = align_pow2(in.requested_size, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
			arena->used    -= (aligned_original - aligned_new);
			out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
		}
		break;

		case AllocatorOp_Rewind:
			farena_rewind(arena, in.save_point);
		break;
		case AllocatorOp_SavePoint:
			out->save_point = farena_save(* arena);
		break;

		case AllocatorOp_Query:
			out->features =
			  AllocatorQuery_Alloc
			| AllocatorQuery_Reset
			| AllocatorQuery_Resize
			| AllocatorQuery_Rewind
			;
			out->max_alloc  = arena->capacity - arena->used;
			out->min_alloc  = 0;
			out->left       = out->max_alloc;
			out->save_point = farena_save(* arena);
		break;
	}
	return;
}
#pragma endregion FArena

#pragma region OS
#pragma warning(push)
#pragma warning(disable: 4820)
#pragma comment(lib, "Kernel32.lib")
#pragma comment(lib, "Advapi32.lib")
#define MS_INVALID_HANDLE_VALUE            ((MS_HANDLE)(__int64)-1)
#define MS_ANYSIZE_ARRAY                   1
#define MS_MEM_COMMIT                      0x00001000
#define MS_MEM_RESERVE                     0x00002000
#define MS_MEM_LARGE_PAGES                 0x20000000
#define MS_PAGE_READWRITE                  0x04
#define MS_TOKEN_ADJUST_PRIVILEGES         (0x0020)
#define MS_SE_PRIVILEGE_ENABLED            (0x00000002L)
#define MS_TOKEN_QUERY                     (0x0008)
#define MS__TEXT(quote)                    L ## quote      // r_winnt
#define MS_TEXT(quote)                     MS__TEXT(quote)   // r_winnt
#define MS_SE_LOCK_MEMORY_NAME             MS_TEXT("SeLockMemoryPrivilege")
typedef int              MS_BOOL;
typedef unsigned long    MS_DWORD;
typedef MS_DWORD*        MS_PDWORD;
typedef void*            MS_HANDLE;
typedef MS_HANDLE*       MS_PHANDLE;
typedef long             MS_LONG;
typedef S8               MS_LONGLONG;
typedef char const*      MS_LPCSTR;
typedef unsigned short*  MS_LPWSTR, *MS_PWSTR;
typedef void*            MS_LPVOID;
typedef MS_DWORD*        MS_LPDWORD;
typedef U8               MS_ULONG_PTR, *MS_PULONG_PTR;
typedef void const*      MS_LPCVOID;
typedef struct MS_SECURITY_ATTRIBUTES *MS_PSECURITY_ATTRIBUTES, *MS_LPSECURITY_ATTRIBUTES;
typedef struct MS_OVERLAPPED          *MS_LPOVERLAPPED;
typedef def_union(MS_LARGE_INTEGER)        { struct { MS_DWORD LowPart; MS_LONG HighPart; } _; struct { MS_DWORD LowPart; MS_LONG HighPart; } u; MS_LONGLONG QuadPart; };
typedef def_struct(MS_FILE)                { void* _Placeholder; };
typedef def_struct(MS_SECURITY_ATTRIBUTES) { MS_DWORD  nLength; MS_LPVOID lpSecurityDescriptor; MS_BOOL bInheritHandle; };
typedef def_struct(MS_OVERLAPPED)          { MS_ULONG_PTR Internal; MS_ULONG_PTR InternalHigh; union { struct { MS_DWORD Offset; MS_DWORD OffsetHigh; } _; void* Pointer; } _; MS_HANDLE  hEvent; };
typedef struct MS_LUID*                    MS_PLUID;
typedef struct MS_LUID_AND_ATTRIBUTES*     MS_PLUID_AND_ATTRIBUTES;
typedef struct MS_TOKEN_PRIVILEGES*        MS_PTOKEN_PRIVILEGES;
typedef def_struct(MS_LUID)                { MS_DWORD LowPart;        MS_LONG HighPart; };
typedef def_struct(MS_LUID_AND_ATTRIBUTES) { MS_LUID  Luid;           MS_DWORD Attributes; };
typedef def_struct(MS_TOKEN_PRIVILEGES)    { MS_DWORD PrivilegeCount; MS_LUID_AND_ATTRIBUTES Privileges[MS_ANYSIZE_ARRAY]; };
__declspec(dllimport) MS_BOOL   __stdcall CloseHandle(MS_HANDLE hObject);
__declspec(dllimport) MS_BOOL   __stdcall AdjustTokenPrivileges(MS_HANDLE TokenHandle, MS_BOOL DisableAllPrivileges, MS_PTOKEN_PRIVILEGES NewState, MS_DWORD BufferLength, MS_PTOKEN_PRIVILEGES PreviousState, MS_PDWORD ReturnLength);
__declspec(dllimport) MS_HANDLE __stdcall GetCurrentProcess(void);
__declspec(dllimport) U8        __stdcall GetLargePageMinimum(void);
__declspec(dllimport) MS_BOOL   __stdcall LookupPrivilegeValueW(MS_LPWSTR lpSystemName, MS_LPWSTR lpName, MS_PLUID lpLuid);
__declspec(dllimport) MS_BOOL   __stdcall OpenProcessToken(MS_HANDLE ProcessHandle, MS_DWORD DesiredAccess, MS_PHANDLE TokenHandle);
__declspec(dllimport) MS_LPVOID __stdcall VirtualAlloc(MS_LPVOID lpAddress, U8 dwSize, MS_DWORD flAllocationType, MS_DWORD flProtect);
__declspec(dllimport) MS_BOOL   __stdcall VirtualFree (MS_LPVOID lpAddress, U8 dwSize, MS_DWORD dwFreeType);
#pragma warning(pop)

typedef def_struct(OS_Windows_State) {
	OS_SystemInfo system_info;
};
global OS_Windows_State os__windows_info;

inline
OS_SystemInfo* os_system_info(void) {
	return & os__windows_info.system_info;
}
inline
void os__enable_large_pages(void) {
	MS_HANDLE token;
	if (OpenProcessToken(GetCurrentProcess(), MS_TOKEN_ADJUST_PRIVILEGES | MS_TOKEN_QUERY, &token))
	{
		MS_LUID luid;
		if (LookupPrivilegeValueW(0, MS_SE_LOCK_MEMORY_NAME, &luid))
		{
			MS_TOKEN_PRIVILEGES priv;
			priv.PrivilegeCount           = 1;
			priv.Privileges[0].Luid       = luid;
			priv.Privileges[0].Attributes = MS_SE_PRIVILEGE_ENABLED;
			AdjustTokenPrivileges(token, 0, & priv, size_of(priv), 0, 0);
		}
		CloseHandle(token);
	}
}
inline
void os_init(void) {
	os__enable_large_pages();
	OS_SystemInfo* info = & os__windows_info.system_info;
	info->target_page_size = (U8)GetLargePageMinimum();
}
// TODO(Ed): Large pages disabled for now... (not failing gracefully)
inline U8 os__vmem_reserve(U8 size, Opts_vmem* opts) {
	assert(opts != nullptr);
	void* result = VirtualAlloc(cast(void*, opts->base_addr), size
		,	MS_MEM_RESERVE
		// |MS_MEM_COMMIT|(opts->no_large_pages == false ? MS_MEM_LARGE_PAGES : 0)
		,	MS_PAGE_READWRITE
	);
	return u8_(result);
}
inline B4 os__vmem_commit(U8 vm, U8 size, Opts_vmem* opts) {
	assert(opts != nullptr);
	// if (opts->no_large_pages == false ) { return 1; }
	B4 result = (VirtualAlloc(cast(MS_LPVOID, vm), size, MS_MEM_COMMIT, MS_PAGE_READWRITE) != 0);
	return result;
}
inline void  os_vmem_release(U8 vm, U8 size) { VirtualFree(cast(MS_LPVOID, vm), 0, MS_MEM_RESERVE); }
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
inline
VArena_R varena__make(Opts_varena_make*R_ opts) {
	assert(opts != nullptr);
	if (opts->reserve_size == 0) { opts->reserve_size = mega(64); }
	if (opts->commit_size  == 0) { opts->commit_size  = mega(64); }
	U8 reserve_size   = align_pow2(opts->reserve_size, os_system_info()->target_page_size);
	U8 commit_size    = align_pow2(opts->commit_size,  os_system_info()->target_page_size);
	B4 no_large_pages = (opts->flags & VArenaFlag_NoLargePages) != 0;
	U8 base           = os_vmem_reserve(reserve_size, .base_addr = opts->base_addr, .no_large_pages = no_large_pages);
	assert(base != 0);
	os_vmem_commit(base, commit_size, .no_large_pages = no_large_pages);
	U8 header_size = align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT);
	VArena_R vm = cast(VArena_R, base);
	vm[0] = (VArena){
		.reserve_start = base + header_size,
		.reserve       = reserve_size,
		.commit_size   = commit_size,
		.committed     = commit_size,
		.commit_used   = header_size,
		.flags         = opts->flags
	};
	return vm;
}
inline
Slice_Mem varena__push(VArena_R vm, U8 amount, U8 type_width, Opts_varena*R_ opts) {
	assert(amount != 0);
	U8 alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8 requested_size = amount * type_width;
	U8 aligned_size   = align_pow2(requested_size, alignment);
	U8 current_offset = vm->reserve_start + vm->commit_used;
	U8 to_be_used     = vm->commit_used   + aligned_size;
	U8 reserve_left   = vm->reserve       - vm->commit_used;
	U8 commit_left    = vm->committed     - vm->commit_used;
	B4 exhausted      = commit_left < to_be_used;
	assert(to_be_used < reserve_left);
	if (exhausted)
	{
		U8 next_commit_size = reserve_left > 0 ?
			max(vm->commit_size, to_be_used)
		:	align_pow2( reserve_left, os_system_info()->target_page_size);
		if (next_commit_size) {
			U8 next_commit_start = u8_(vm) + vm->committed;
			B4 no_large_pages    = (vm->flags & VArenaFlag_NoLargePages) != 0;
			B4 commit_result     = os_vmem_commit(next_commit_start, next_commit_size, .no_large_pages =  no_large_pages);
			if (commit_result == false) {
				return (Slice_Mem){0};
			}
			vm->committed += next_commit_size;
		}
	}
	vm->commit_used = to_be_used;
	return (Slice_Mem){.ptr = current_offset, .len = requested_size};
}
inline void varena_release(VArena_R arena) { os_vmem_release(u8_(arena), arena->reserve); }
inline Slice_Mem varena__shrink(VArena_R vm, Slice_Mem old_allocation, U8 requested_size, Opts_varena* opts) {
	assert(opts != nullptr);
	Slice_Mem result = {0};
	U8 current_offset = vm->reserve_start + vm->commit_used;
	U8 shrink_amount  = old_allocation.len - requested_size;
	if (lt_s(shrink_amount, 0)) {
		result = old_allocation;
		return result;
	}
	assert(old_allocation.ptr == current_offset);
	vm->commit_used -= shrink_amount;
	result           = (Slice_Mem){ old_allocation.ptr, requested_size };
	return result;
}
inline
void varena_rewind(VArena* vm, AllocatorSP sp) {
	assert(vm != nullptr);
	assert(sp.type_sig == & varena_allocator_proc);
	vm->commit_used = max(sp.slot, sizeof(VArena));
}
inline AllocatorSP varena_save(VArena* vm) { return (AllocatorSP){varena_allocator_proc, vm->commit_used}; }
void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	VArena* vm = cast(VArena*, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = varena_push_mem(vm, in.requested_size, .alignment = in.alignment);
			memory_zero(out->allocation.ptr, out->allocation.len * in.op);
		break;

		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			vm->commit_used = 0;
		break;

		case AllocatorOp_Grow_NoZero:
		case AllocatorOp_Grow: {
			U8 grow_amount = in.requested_size - in.old_allocation.len;
			if (grow_amount == 0) {
				out->allocation =  in.old_allocation;
				return;
			}
			U8 current_offset = vm->reserve_start + vm->commit_used;
			// Growing when not the last allocation not allowed
			assert(in.old_allocation.ptr == current_offset);
			Slice_Mem allocation = varena_push_mem(vm, grow_amount, .alignment = in.alignment);
			assert(allocation.ptr != 0);
			out->allocation = (Slice_Mem){ in.old_allocation.ptr, in.requested_size };
			memory_zero(out->allocation.ptr, out->allocation.len * (in.op - AllocatorOp_Grow_NoZero));
		}
		break;
		case AllocatorOp_Shrink: {
			U8 current_offset = vm->reserve_start     + vm->commit_used;
			U8 shrink_amount  = in.old_allocation.len - in.requested_size;
			if (lt_s(shrink_amount, 0)) {
				out->allocation = in.old_allocation;
				return;
			}
			assert(in.old_allocation.ptr == current_offset);
			vm->commit_used -= shrink_amount;
			out->allocation = (Slice_Mem){ in.old_allocation.ptr, in.requested_size };
		}
		break;

		case AllocatorOp_Rewind:
			vm->commit_used = in.save_point.slot;
		break;
		case AllocatorOp_SavePoint:
			out->save_point = varena_save(vm);
		break;

		case AllocatorOp_Query:
			out->features =
				AllocatorQuery_Alloc
			|	AllocatorQuery_Resize
			|	AllocatorQuery_Reset
			|	AllocatorQuery_Rewind
			;
			out->max_alloc  = vm->reserve - vm->committed;
			out->min_alloc  = kilo(4);
			out->left       = out->max_alloc;
			out->save_point = varena_save(vm);
		break;
	}
}
#pragma endregion VArena

#pragma region Arena (Chained Arena)
inline
Arena_R arena__make(Opts_arena_make*R_ opts) {
	assert(opts != nullptr);
	U8 header_size = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	VArena* current = varena__make(opts);
	assert(current != nullptr);
	Arena* arena = varena_push(current, Arena);
	* arena = (Arena){
		.backing  = current,
		.prev     = nullptr,
		.current  = arena,
		.base_pos = 0,
		.pos      = header_size,
		.flags    = opts->flags,
	};
	return arena;
}
Slice_Mem arena__push(Arena_R arena, U8 amount, U8 type_width, Opts_arena* opts) {
	assert(arena != nullptr);
	assert(opts  != nullptr);
	Arena_R active        = arena->current;
	U8 size_requested = amount * type_width;
	U8 alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8 size_aligned   = align_pow2(size_requested, alignment);
	U8 pos_pre        = active->pos;
	U8 pos_pst        = pos_pre + size_aligned;
	B4 should_chain =
		((arena->flags & ArenaFlag_NoChain) == 0)
	&&	active->backing->reserve < pos_pst;
	if (should_chain)
	{
		Arena* new_arena = arena_make(
			.base_addr    = 0,
			.reserve_size = active->backing->reserve,
			.commit_size  = active->backing->commit_size,
			.flags        = active->backing->flags,
		);
		new_arena->base_pos = active->base_pos + active->backing->reserve;
		sll_stack_push_n(arena->current, new_arena, prev);
		active = arena->current;
	}
	U8         result = u8_(active) + pos_pre;
	Slice_Mem vresult = varena_push_mem(active->backing, size_aligned, .alignment = alignment);
	slice_assert(vresult);
	assert(result == vresult.ptr);
	active->pos = pos_pst;
	return vresult;
}
inline
void arena_release(Arena* arena) {
	assert(arena != nullptr);
	Arena_R curr = arena->current;
	Arena_R prev = nullptr;
	for (; curr != nullptr;	curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
}
inline void arena_reset(Arena* arena) { arena_rewind(arena, (AllocatorSP){.type_sig = arena_allocator_proc, .slot = 0}); }
void arena_rewind(Arena* arena, AllocatorSP save_point) {
	assert(arena != nullptr);
	assert(save_point.type_sig == arena_allocator_proc);
	U8      header_size = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	Arena_R curr        = arena->current;
	U8      big_pos     = clamp_bot(header_size, save_point.slot);
	for (Arena_R prev = nullptr; curr->base_pos >= big_pos; curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
	arena->current = curr;
	U8 new_pos = big_pos - curr->base_pos;
	assert(new_pos <= curr->pos);
	curr->pos = new_pos;
	varena_rewind(curr->backing, (AllocatorSP){varena_allocator_proc, curr->pos + size_of(VArena)});
}
inline AllocatorSP arena_save(Arena_R arena) { return (AllocatorSP){arena_allocator_proc, arena->base_pos + arena->current->pos}; }
void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	assert(out != nullptr);
	Arena* arena = cast(Arena*, in.data);
	assert(arena != nullptr);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation       = arena_push_mem(arena, in.requested_size, .alignment = in.alignment);
			memory_zero(out->allocation.ptr, out->allocation.len * in.op);
		break;
		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			arena_reset(arena);
		break;

		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero: {
			Arena_R active = arena->current;
			U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
			U8 arena_end = u8_(active) + active->pos;
			if (alloc_end == arena_end)
			{
				U8 grow_amount  = in.requested_size - in.old_allocation.len;
				U8 aligned_grow = align_pow2(grow_amount, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
				if (active->pos + aligned_grow <= active->backing->reserve)
				{
					Slice_Mem vresult = varena_push_mem(active->backing, aligned_grow, .alignment = in.alignment);
					if (vresult.ptr != null)
					{
						active->pos          += aligned_grow;
						out->allocation       = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
						out->continuity_break = false;
						memory_zero(in.old_allocation.ptr + in.old_allocation.len, grow_amount * in.op - AllocatorOp_Grow_NoZero);
						break;
					}
				}
			}
			Slice_Mem new_alloc = arena__push(arena, in.requested_size, 1, &(Opts_arena){.alignment = in.alignment});
			if (new_alloc.ptr == null) {
				out->allocation = (Slice_Mem){0};
				break;
			}
			memory_copy(new_alloc.ptr, in.old_allocation.ptr, in.old_allocation.len);
			memory_zero(new_alloc.ptr + in.old_allocation.len, (in.requested_size - in.old_allocation.len) * in.op - AllocatorOp_Grow_NoZero);
			out->allocation = new_alloc;
			out->continuity_break = true;
		}
		break;

		case AllocatorOp_Shrink: {
			Arena_R active = arena->current;
			U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
			U8 arena_end = u8_(active) + active->pos;
			if (alloc_end != arena_end) {
				out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
				break;
			}
			//SSIZE shrink_amount    = in.old_allocation.len - in.requested_size;
			U8 aligned_original = align_pow2(in.old_allocation.len, MEMORY_ALIGNMENT_DEFAULT);
			U8 aligned_new      = align_pow2(in.requested_size, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
			U8 pos_reduction    = aligned_original - aligned_new;
			active->pos           -= pos_reduction;
			varena__shrink(active->backing, in.old_allocation, in.requested_size, &(Opts_varena){.alignment = in.alignment});
			out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
		}
		break;

		case AllocatorOp_Rewind:
			arena_rewind(arena, in.save_point);
		break;

		case AllocatorOp_SavePoint:
			out->save_point = arena_save(arena);
		break;
		case AllocatorOp_Query:
			out->features =
				AllocatorQuery_Alloc
			|	AllocatorQuery_Resize
			|	AllocatorQuery_Reset
			|	AllocatorQuery_Rewind
			;
			out->max_alloc  = arena->backing->reserve;
			out->min_alloc  = kilo(4);
			out->left       = out->max_alloc - arena->backing->commit_used;
			out->save_point = arena_save(arena);
		break;
	}
}
#pragma endregion Arena

// C--
#pragma region Key Table 1-Layer Linear (KT1L)
void kt1l__populate_slice_a2(KT1L_Byte*R_ kt, AllocatorInfo backing, KT1L_Meta m, Slice_Mem values, U8 num_values ) {
	assert(kt != nullptr);
	if (num_values == 0) { return; }
	kt[0] = mem_alloc(backing, m.slot_size * num_values ); slice_assert(* kt);
	U8 iter = 0;
	loop: {
		U8 slot_offset = iter        * m.slot_size;       // slot id
		U8 slot_cursor = kt->ptr     + slot_offset;       // slots[id]            type: KT1L_<Type>
		U8 slot_value  = slot_cursor + m.kt_value_offset; // slots[id].value      type: <Type>
		U8 a2_offset   = iter        * m.type_width * 2;  // a2 entry id
		U8 a2_cursor   = values.ptr  + a2_offset;         // a2_entries[id]       type: A2_<Type>
		U8 a2_value    = a2_cursor   + m.type_width;      // a2_entries[id].value type: <Type>
		memory_copy(slot_value, a2_value, m.type_width);  // slots[id].value = a2_entries[id].value
		u1_r(slot_cursor)[0] = 0; 
		hash64_djb8(u8_r(slot_cursor), slice_mem(a2_cursor, m.type_width)); // slots[id].key   = hash64_djb8(a2_entries[id].key)
		++ iter;
		if (iter < num_values) goto loop;
	}
	kt->len = num_values;
}
#pragma endregion KT1L

#pragma region Key Table 1-Layer Chained-Chunked_Cells (KT1CX)
inline
void kt1cx_init(KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte* result) {
	assert(result                  != nullptr);
	assert(info.backing_cells.proc != nullptr);
	assert(info.backing_table.proc != nullptr);
	assert(m.cell_depth     >  0);
	assert(m.cell_pool_size >= kilo(4));
	assert(m.table_size     >= kilo(4));
	assert(m.type_width     >  0);
	result->table     = mem_alloc(info.backing_table, m.table_size * m.cell_size);      slice_assert(result->table);
	result->cell_pool = mem_alloc(info.backing_cells, m.cell_size  * m.cell_pool_size); slice_assert(result->cell_pool);
	result->table.len = m.table_size; // Setting to the table number of elements instead of byte length.
}
void kt1cx_clear(KT1CX_Byte kt, KT1CX_ByteMeta m) {
	U8 cell_cursor = kt.table.ptr;
	U8 table_len   = kt.table.len * m.cell_size;
	for (; cell_cursor != slice_end(kt.table); cell_cursor += m.cell_size ) // for cell in kt.table.cells
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size }; // slots = cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor < slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			Slice_Mem slot = {slot_cursor, m.slot_size}; // slot = slots[id]
			memory_zero(slot.ptr, slot.len);             // clear(slot)
		}
		U8 next = slot_cursor + m.cell_next_offset; // next = slots + next_cell_offset
		if (next != null) {
			slots.ptr   = next; // slots = next
			slot_cursor = next;
			goto process_slots;
		}
	}
}
inline
U8 kt1cx_slot_id(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta m) {
	U8 hash_index = key % kt.table.len;
	return hash_index;
}
U8 kt1cx_get(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta m) {
	U8 hash_index  = kt1cx_slot_id(kt, key, m);
	U8 cell_offset = hash_index * m.cell_size;
	U8 cell_cursor = kt.table.ptr + cell_offset; // KT1CX_Cell_<Type> cell = kt.table[hash_index]
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size}; // KT1CX_Slot_<Type>[kt.cell_depth] slots = cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot* slot = cast(KT1CX_Byte_Slot*, slot_cursor + m.slot_key_offset); // slot = slots[id]     KT1CX_Slot_<Type>
			if (slot->occupied && slot->key == key) {
				return slot_cursor;
			}
		}
		U8 cell_next = cell_cursor + m.cell_next_offset; // cell.next
		if (cell_next != null) {
			slots.ptr   = cell_next; // slots = cell_next
			slot_cursor = cell_next;
			cell_cursor = cell_next; // cell = cell_next
			goto process_slots;
		}
		else {
			return null;
		}
	}
}
inline
U8 kt1cx_set(KT1CX_Byte kt, U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta m) {
	U8 hash_index  = kt1cx_slot_id(kt, key, m);
	U8 cell_offset = hash_index * m.cell_size;
	U8 cell_cursor = kt.table.ptr + cell_offset; // KT1CX_Cell_<Type> cell = kt.table[hash_index]
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size}; // cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot_R slot = cast(KT1CX_Byte_Slot_R, slot_cursor + m.slot_key_offset);
			if (slot->occupied == false) {
				slot->occupied = true;
				slot->key      = key;
				return slot_cursor;
			}
			else if (slot->key == key) {
				return slot_cursor;
			}
		}
		KT1CX_Byte_Cell curr_cell = { cell_cursor + m.cell_next_offset }; // curr_cell = cell
		if ( curr_cell.next != null) {
			slots.ptr   = curr_cell.next;
			slot_cursor = curr_cell.next;
			cell_cursor = curr_cell.next;
			goto process_slots;
		}
		else {
			Slice_Mem new_cell = mem_alloc(backing_cells, m.cell_size);
			curr_cell.next     = new_cell.ptr;
			KT1CX_Byte_Slot_R slot = cast(KT1CX_Byte_Slot_R, new_cell.ptr + m.slot_key_offset);
			slot->occupied = true;
			slot->key      = key;
			return new_cell.ptr;
		}
	}
	assert_msg(false, "impossible path");
	return null;
}
#pragma endregion Key Table



#pragma endregion Implementation

int main(void)
{
	U8 a = 4;
	U8 b = 2;
	a = add_s(a, b);
	U8 test = ge_s(a, b);
	return 0;
}

#pragma clang diagnostic pop

# watl.v0.msvc.c Docs

Documention for the file is kept separate for the sake of compact definitions.

## Organization

The file is segregated with region pragmas with the following hierarchy

* DSL: Intrinsic includes, typedefs, and macros to make C more ergonomic to write and read.
* Memory: Basic memory operations and slice definitions
* Strings: Definition of UTF-8 strings.
* Allocator Interface: Generalized runtime allocator interface definitions
* Hashing: Cryptographic hashing definitions (only `hash64_djb8`)
* Key Tables: KT1L & KT1LCX generic hash table definitions
* String Operations: Basic String Ops & String Generation
* Debug: Runtime assertion definitions
* File System: File I/O
* WATL: Lexer & Parser definitons for the WATL format
* Implementation: Resolving all definitions that were originally just forward signatures before. Preserves the order of the above with sub-regions.

## Macro Usage

There is an attempt to keep macro usage to a low-degree of concatenation. Most of the macros consist of at most 3-4 layers of expansion with the majority of n-layers of expressions beyond the first being related to the usage of:

* glue: Like tmpl but for arbitrary concatentation of symbols
* optional_args: Used with functional macros implementing the optional arg pattern.
* def_struct: Used with-in def_range, def_slice as a secondary expansion
* tmpl: Used with templating definitions not utilizing a stage metaprogram to define.
	* Can be found at arbitrary expansion depths.

### Macros of notable complexity

#### optional_args(symbol, ...)

In C, there is no-language provided feature for optional arguments in the sense where you can in C++ do:

```c
 void Options(int some_param = 4);
 ```

 Instead, the preprocessor can be utilized with a quirk of the struct temporary initialization syntax:

 ```c
typedef struct Options; struct Options {
	int some_param;
};
void do_something(Options* optional)
void example {
	do_something(& (Options){});
	// or
	do_something(& (Options){.some_param = 1});
}
 ```

 In the above case, we can directly define a value for the optional pointer. The compiler will automatically initialize the struct and place on the stack for the lifetime of the `do__something`'s scope; while also providing the procedure an address to it.

 Because its valid to have no arguments within the braces of the struct initalization we can utilize the following expansion:

```c
&(symbol){ __VA_ARGS__ }
```

Where the __VA_ARGS__ can be any valid syntax for initializing the struct's members.

The following convention can be used for any procedure we would like optional arguments for:

```c
typedef struct Options; struct Options {
	int some_param;
};
void do___something(Options* opts)
#define do_something(...) do__something(&(Options){__VA_ARGS__})
```

To signify intent we utilize the macro:

```c
#define optional_args(...) &(symbol){__VA_ARGS__}
#define do_something(...) proc_identifier(optional_args(Options, __VA_ARGS__))
void example {
	do_something();
	// or
	do_something(.some_param = 1);
}
```

### slice_arg_from_array

This exercise makes heavy use of the slice pattern:

```c 
struct Slice_<type> { type* ptr; SSIZE len; }
```

We can utilize an array initalization pattern with slices to behave as an alternative to varadic arguments.

```c
#define lit(str) (Str8){ str, size_of(str) - 1 };
typedef struct Str8       Str8;       struct       Str8 { UTF8* ptr; SSIZE len; }; 
typedef struct Slice_Str8 Slice_Str8; struct Slice_Str8 { Str8* ptr; SSIZE len; };
void str8_fmt(Str8 fmt_template, Slice_Str8* args);
void example {
	str8_fmt(lit("Hello str8_fmt: <an_arg>"), &(Slice_Str8) {
		.ptr = (Str8[]){ lit("an_arg"), lit("a subst!") },
		.len = (SSIZE)sizeof( (Str8[]){ lit("an_arg"), lit("a subst!") } ) / size_of(Str8)
	});
}
```

In the above, we utilized the same temporary value pattern we did with structs for optional arguments, but now for a fixed-size stack array. Naturally without the preprocessor, its far too tedius to write the out:

```c
#define tmpl(prefix, type) prefix ## _ ## type
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) {    \
	.ptr = (type[]){__VA_ARGS__},                                 \
	.len = (SSIZE)sizeof( (type[]){__VA_ARGS__} ) / size_of(type) \
}
void example {
	str8_fmt(lit("hello str8_fmt: <an_arg>"), slice_arg_from_array(
		lit("an_arg"), lit("a subst!")
	));
	// or
	str8_fmt(lit("hello str8_fmt: <an_arg>"), slice_arg_from_array());
}
```

To make it more ergonomic we embed the slice_arg_from_array into the frontend macro for the procedure like before for optionals:

```c
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) {    \
	.ptr = (type[]){__VA_ARGS__},                                 \
	.len = (SSIZE)sizeof( (type[]){__VA_ARGS__} ) / size_of(type) \
}
void str8__fmt(Str8 fmt_template, Slice_Str8* args);
#define str8_fmt(fmt_template, ...) str8__fmt(fmt_template, slice_arg_from_array(__VA_ARGS__))
void example {
	str8_fmt(lit("hello str8_fmt: <an_arg>"),
		lit("an_arg"), lit("a subst!")
	);
	// or
	str8_fmt(lit("hello str8_fmt: <an_arg>"));
}
```

The actual macro uses farray helper macros:

```c
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) {  \
	.ptr = farray_init(type, __VA_ARGS__),                      \
	.len = farray_len( farray_init(type, __VA_ARGS__)           \
}
```

### Type definition helpers

`def_enum` and `def_struct` are used to reduce the redundancy of having to typedef a struct definition in order to expose it to the translation unit's namespace.  
For enums, we specify the underlying type then begin the `enum` keyword and follow with defining the enum values.

```c
#define def_struct(symbol)                  struct symbol symbol;   struct symbol
#define def_enum(underlying_type, symbol)   underlying_type symbol; enum   symbol
```

### Iteration helpers

`range_iter` & `slice_iter` are utilized for simplifying for-loop iteration with a macro to help reduce user-error.

`range_iter` is used with Range types that must be defined ahead of type by the user with `def_range`.  
`def_range` produces both a `Range_<type>` type and a `Iter_Range_<type>` type, the `Iter_Range_<type>` contains the range along with a cursor.

## Procedure Signature Convention

Inline procedures without optionals are as usual.  

Procedures which behave as initializer have two formats:

```c
void <prefix>_init(<struct>* data, ...);
<struct> <prefix>_make(...);
```

`<prefix>_init` lets the user define where struct lives, while `<prefix>_make` will allocate at minimum a temporary on the stack.

A third type is exported symbols. These have `api_<prefix>_<symbol>` as their conventional name.
They follow a similar pattern to `<prefix>_init` except they're meant to be used as cold procedures which heavy amounts of data passed into them or formatted out to the user via *"out"* parameters.

Generally if a process from a heavy procedure can support graceful failures, then a `struct <prefix>_<symbol>Info` will be utilized as an encapsulated payload for the user. It will contain a slice or linked-list of messages along with an aggregate set of top-level status signals on how the process went along with the intended payload the user wanted resolved for the operation.

The WATL Lexer & Parser will use this API convention.  
The File System api wrapper however will not support messaging or a signal state (just returns null on failures).

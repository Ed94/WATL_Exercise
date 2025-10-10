# WATL Exercise

An exercise on making the "Whitespace Aware Text Layout" parser with different languages or conventions. It simply gets a structural idea of the lines and chunks (visbile and whitespace) for a text file.  
The purpose of this exercise is convey succiently many core pragmatic concepts for code in a small program.  
The intent was to use this as a working set of samples for my code visualizing and editing prototyping.

The code conveys a convention for doing "systems" programming I've synthesized after studying how several people in the "handmade" community have written their exposed libraries or codebases.

The goal of the exercise is always the following:

```odin
start:
    file_contents := file.read_contents(self.source)
    tokens        := watl.lex(file_contents)
    str_cache     := str.cache.init()
    lines         := watl.parse(tokens)
    listing       := watl.dump_listing(lines)
    file.write_str(str.fmt("<name>.listing.source", self.source.name))
end
```

There are plans for multiple versions of the program:

* V0: Attempt todo a single-threaded example with as little support from the toolchain as possible within the domain of the language. With a single compilation stage.
* V1: Same as above just multi-threaded. (Subject to change)
* V2: 2-Stage compilation using a user defined metaprogram written in the same language platform (except for assembly).
  * This is to manually control symbol generation.

V2s will most likely not be done for the majority of languages on here unless there is a stage metaprogramming library or functionality for the target platform avaialble.

FORTH will be bootstrapped from scratch jonesforth style as thats the correct way to use forth (author's current take..)
Embeddable scripting languages will be embedded as they should be.

## TODOs

* Fix large-pages not working (at least on my system).

* [x] Single-threaded C example
* [] Multi-threaded C example
* [] Add basic timing benchmark to C examples
* [] Add profiling support C examples
* [x] Single-threaded Odin example
* [] Single-threaded Odin ideomatic example
* [] Add basic timing benchmark to Odin examples
* [] Add profiling support Odin examples
* [] Single-threaded nasm example
* [] Multi-threaded nasm example
* [] Single-threaded FORTH example
* [] Multi-threaded FORTH example
* [] Single-threaded lua example
* [] Multi-threaded lua example

### Maybe

* [] Make C++ examples
* [] Add basic timing benchmark to C++ examples
* [] Add profiling support C++ examples
* [] Single-threaded C# example
* [] Multi-threaded C# example
* [] Single-threaded F# example
* [] Multi-threaded F# example
* [] Single-threaded umka example
* [] Multi-threaded umka example

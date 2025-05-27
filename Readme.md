# WATL Exercise

An exercise on making the simplest useful parser with different languages or conventions.

The C code conveys a convention for doing C I've synthesized after studying how several people in the "handmade" community have written their exposed libraries or codebases.

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

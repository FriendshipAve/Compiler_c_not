# Compiler for `C-not`, a subset of C
This is a compiler for C0, as specified by the [link](https://c0.cs.cmu.edu/) here.
This compiler also supports a special ADT design, as we call it as `L6`.

## Author
Tianwei Li

Yicheng Zhang (`zyc`at`cmu.edu`)

### Version and Dependency
This code was tested against Stable Rust (1.45.2). Other than `serde_json`, which was required only for one checkpoint during development, it has no dependencies other than `std`, which allows it to compile quite quickly. 


### Command line 
The followings are applicable command-line flags and their meanings: 
- `-ts`: emit token stream
- `-ast0`: emit unelaborated AST
- `-elab`: emit elaborated AST
- `-eabs`: emit abstract assembly
- `-ebbgraph`: emit basicblock graph
- `-elive`: emit liveness analysis
- `-egraph`: emit variable interference graph
- `-ereg`: emit register allocation mapping
- `-eregsub`: emit abstract assembly, except with all temporaries substituted with their regalloc assignments.
- `-ex86-64`: emit x86-64 assembly.

### Run tests

- Issuing the shell command `% make` should generate the appropriate files so that `% bin/c0c --exe <args>` will run the compiler and produce an executable. 
- The command `% make clean` should remove all binaries, heaps, and other generated files.

If you use OS X, you will need to output slightly different assembly (error codes and labels will be different). Please go to `./lab6/src/util/c0spec.rs` and change `MAC` to be true.

### Compiler Structure

#### Driver

- **Main** (`main.rs`): Spawns a new child thread and runs the compile cycle,
  returning appropriate error codes.
- **Args** (`args.rs`): Parses command line arguments.

#### Passes

- **Lexer** (`lex.rs`): Reads a stream of characters from source files, and parses them into tokens recognized by the C0 grammar lazily every time that `token()` is called. Returns `Err(Error::EOF)` when done. This keeps track of a running line number and character position, and helps emit useful messages that pinpoints the sourcefile syntactic error location.
- **Parser** (`parse.rs`): Recursive descent parser, constructs an AST from the
  C0 grammar. Makes use of a modular $n$-lookahead buffer. The code structure matches the grammar almost exactly, except for handling of expression operator precedence, which is done in manual tiers.
- **AST** (`ast.rs`): Type definitions for a C0 Abstract Syntax Tree
  representation.
- **Elaboration** (`elab.rs`): Elaboration pass for Abstract Syntax Tree, which explicitly represents variable scopes, and converts control flow structures like `for` / `if` / `terop` into their naïve version.
- **Type Checking** (`tc/*.rs`): Verify that the AST with a function is a valid program that
  conforms to C0 static semantics, particularly regarding variable declaration and definition, global type definitions, function declarations, etc. 
- **ASM** (`asm.rs`): Type definitions for bytecode-like abstract assembly
  syntax that uses 3-address operations and an infinite number of temporary virtual registers. This is a useful IR for optimization passes and SSA conversion. It also contains the uses / defines of each instruction, which is useful for liveness analysis.
- **Codegen** (`codegen.rs`): Translates the AST into flattened abstract assembly. It wraps effectful operations like div / shift with appropriate checks, and outlines the general assembly structure before / after function call.
- **Register Allocation** (`reg_alloc/*.rs`, `asm_processing/*.rs`): Converts the IR into a graph of basic blocks, performs liveness analysis, and allocates registers via graph coloring. 
- **Assembly** (`assembly.rs`): Type definitions for x86 assembly instructions.
- **X86 Assemlby Generation** (`asm_to_assem/*.rs`): Converts the IR into corresponding x86 assembly instructions. It handles explicit details like computing stack location, aligning function call, variable / register size, etc. 
- **Emit** (`emit.rs`): Writes a variety of output to a target file. It can emit x86 assembly and abstract assembly, and can also emit AST / liveness analysis lines / register allocation result for debugging purposes.

#### Helpers

- **Errors** (`error.rs`): Defines a basic error & result type so that we can
  make use of the `?` symbol for clean result handling (as opposed to dealing
  with options everywhere).
- **Checkpoint** (`checkpoint.rs`): Deserializes and serializes the checkpoint
  format and has a place to actually implement the checkpoint, which is run
  from main when the compiler is run in checkpoint mode.
- **Constant parameters** (`const_params.rs`): Holds variables that influences the behavior of the compiler, i.e. register count threshold for regalloc pass.
- **Utils** (`util/*.rs`): Utilities such as a peek-buffer datastructure, some C0-related parameters, etc.

### Other Information
We have included a script, `bin/compile` that will run your compiler and then
actually create an executable. This can be helpful when debugging. You can
also compile and run a file using the `-x` flag.


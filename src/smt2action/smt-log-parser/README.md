# Rust Axiom Profiler prototype

### Installation and requirements
- Clone this repository. This repository uses Git LFS (https://git-lfs.com/) as some log files are too large to push to GitHub with regular Git (>100 MiB) and so it is necessary to install Git LFS to properly retrieve all the Z3 log files as text.
- Graphviz is needed to render SVG images. See https://www.graphviz.org/download/.
- It is recommended to install a linker such as `lld` or `mold` to speed up Rust compilation (see https://nnethercote.github.io/perf-book/compile-times.html). If not using `mold`, the rustflags line of `.cargo/config.toml` must be changed; for example, with `lld`` it should instead be: 

    ```rustflags = ["-C", "link-arg=-fuse-ld=lld"]```

    If using the default linker, remove the line.
- To compile and run the parser directly, enter `cargo run --bin prototype` in the terminal while in the top-level directory of the project. Currently, this particular binary does not provide a way to *manually* stop parsing (skip remaining lines) and have the program continue.
### Actix server
- In the top-level directory of the project, enter `cargo run --bin actix-server` in terminal to start the server. It will not do anything on its own or accept any input other than HTTP requests (e.g. requests made by the accompanying Yew frontend or Linux's `curl`).
- The server will remain active until stopped manually (i.e. Ctrl+C or Cmd+C). If a panic occurs in parsing/outputting/rendering, the server seems to still respond to new requests.

### Yew frontend
- See https://github.com/richardluo20/axiom-profiler-yew-GUI/ for repo and instructions.
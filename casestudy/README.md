# ilc-haskell

Incremental lambda calculus in Haskell

## Installation

### Installation with [`stack`](https://docs.haskellstack.org/en/stable/README/)

```
stack install --test
```

Tested with `stack` version 1.6.5.

### Installation with [`cabal`](https://www.haskell.org/cabal/download.html)

Requires [`ghc` version 8.2.2](https://www.haskell.org/ghc/download_ghc_8_2_2.html).

```
cabal sandbox init
cabal install -w /path/to/ghc-8.2.2 --enable-tests --enable-benchmarks
```

Tested with `cabal` 1.24.0.2.

## Running the benchmarks

You should have two executables either in `.local/bin` or in `.cabal-sandbox/bin/`:

- `graph-results`: Runs the full case study. Input sizes are hard-coded in `benchmark-src/GraphResults.hs`. Timing results will be found in `benchmark-results/map/indexedJoin.csv` for example. Space results will be found in `benchmark-results/map/indexedJoin_space.csv` for example. If you want to rerun the case study you have to delete or rename the `benchmark-results` folder.

- `generate`: Prints the generated code to stdout.

## Overview

- `library-src/`: An implementation of primitives and their CTS and CTS derivatives.
- `executable-src/StaticCaching.hs`: And implementation of LambdaAL and generation of original, CTS and CTS derivative code.
- `executable-src/Generate.hs`: Generate code and print to stdout.
- `extecutable-src/Examples/`: Source programs.
- `generated-src/`: Generated code.
- `test-src/`: A test suite for primitives and generated code.
- `benchmark-src/Benchmark.hs`: Benchmarks used internally for performance assessment.
- `benchmark-src/GraphResults.hs`: Run benchmarks that we report and extract results into CSV files.
- `raw-benchmark-results/`: Raw results that we reported.


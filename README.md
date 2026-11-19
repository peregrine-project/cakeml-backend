# CakeML backend for Peregrine

## Meta

- Author(s):
  - Hugo Segoufin-Cholet ([**@hsegoufin**](https://github.com/hsegoufin))
- Maintainer:
  - Yannick Forster ([**@yforster**](https://github.com/yforster))
- License: [MIT License](LICENSE)
- Compatible Rocq versions: 9.0-9.1

## CakeML-related files

The files in `theories/CakeML` are arranged to mirror the structure of  [CakeML](https://github.com/CakeML/cakeml/tree/e1650fc504837c0fbd3931cc5066914ffdc9d877).
- [ast.v]( https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/ast.v ) : the basic defintions
- [functions.v](https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/functions.v) : some generic functions and relations.
- [namespace.v](https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/namespace.v) : the definitoons and funcions to manipulate namespace
- [semanticPrimitives.v](https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/semanticPrimitives.v) : all the other helpers functions
- [smallstep.v](https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/smallstep.v) : a functionnal small-step semantic for CakeML
- [smallstep_rel.v]( https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/smallstep_rel.v) : a relationnal small-step semantic for CakeML
- [bigstep.v](https://github.com/peregrine-project/cakeml-backend/blob/main/Exceptions/bigstep.v) : a relationnal big-step semantic for CakeML
- [Proofs](https://github.com/peregrine-project/cakeml-backend/tree/main/Exceptions/proofs) : The equivalence proofs

## Backend

The other files in `theories` are similar to `rocq-verified-extraction`:

- `FFI.v` is an administrative file
- `Compile.v` has the compilation function
- `CompileCorrect.v` proves the compilation function correct
- `Pipeline.v` has the MetaRocq pipeline instantiated
- `PipelineCorrect.v` has the end-to-end correctness theorem `verified_cakeml_pipeline_theorem`
- `Serialize.v` has a printer to s-expressions

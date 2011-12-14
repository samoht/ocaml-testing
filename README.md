This compiler branch change the way location information in the
lambda-code is handled with -g. Instead of using Levents, the
Lambda.lamda type is changed to be a record containing the description
of the lambda-term and the location information.

STATUS
------

* the bytecode backend compiles; need to check further is the
  semantics ocamldebug is preserved
* the  native backend is broken
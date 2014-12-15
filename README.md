lazyKoq
=======

interpreter of lazy K written by Coq and OCaml

Environment
-----------
OCaml 4.01.0  
Coq 8.4pl3
OMake 0.9.8.5

Build
-----
`./make.sh`

Output
------
lazykoq.opt (bytecode)  
lazykoq.run (nativecode)

usage
-----

echo "Hello, LazyKoq" | ./lazykoq.opt ./sample/echo.lazy  
 #=> "Hello, LazyKoq"

versions:
- Coq 8.5pl2
- a recent version (august 2016) of the Mathematical Component library
  https://github.com/math-comp/math-comp

installation:
1. add to the _CoqProject file the position of the MathComp library
   e.g., -R "~/math-comp/mathcomp" mathcomp
2. generate the Makefile using coq_makefile
   e.g., coq_makefile -f _CoqProject -o Make
3. make -f Make

boolp.v, reals.v are included for convenience,
they come from
https://github.com/strub/coq-alternate-reals
by P.-Y. Strub

some references used in this work:
[murray] Murray, Li, Shankar Sastry: A Mathematical Introduction to Robotic Manipulation
[springer] Siciliano, Khatib (Eds.): Springer Handbook of Robotics
[angeles] Angeles: Fundamentals of Robotic Mechanical Systems
[oneill] O'Neill: Elementary Differential Geometry
[spong] Spong, Hutchinson, Vidyasagar: Robot Modeling and Control

{ lib, mkCoqDerivation, coq
, hierarchy-builder
, mathcomp-ssreflect, mathcomp-fingroup, mathcomp-algebra
, mathcomp-solvable, mathcomp-field, mathcomp-analysis
, mathcomp-real-closed, mathcomp-algebra-tactics
}:

mkCoqDerivation {
  pname = "robot-rocq";
  owner = "affeldt-aist";
  version = "dev";
  src = ../../..;

  propagatedBuildInputs = [
    hierarchy-builder
    mathcomp-ssreflect
    mathcomp-fingroup
    mathcomp-algebra
    mathcomp-solvable
    mathcomp-field
    mathcomp-analysis
    mathcomp-real-closed
    mathcomp-algebra-tactics
  ];

  meta = {
    description = "Formal Foundations for Modeling Robot Manipulators";
    license = lib.licenses.lgpl21Plus;
  };
}
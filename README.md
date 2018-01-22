Formal Foundations for Modeling Robot Manipulators
====

## Contents

This library is a formalization of the mathematics of rigid body
transformations in the Coq proof-assistant. It can be used to address
the forward kinematics problem of robot manipulators. It contains
theories for angles, three-dimensional geometry (including
three-dimensional rotations, skew-symmetric matrices, quaternions),
rigid body transformations (isometries, homogeneous representation,
Denavit-Hartenberg convention, screw motions), and an application to
the SCARA robot manipulator.

## License

The license for this library's original contents is LGPL v3
(https://www.gnu.org/copyleft/lesser.html).

## Authors

see [AUTHORS.md](AUTHORS.md)

## Files

see [FILES.md](FILES.md)

## Requirements

* The Coq proof-assistant (v8.7)
  https://coq.inria.fr/
* The Mathematical Components library
  https://github.com/math-comp/math-comp
* The coq-alternate-reals library 
  https://github.com/strub/coq-alternate-reals

## Installation Procedure

see [INSTALL.md](INSTALL.md)

## References

Main reference:
* Reynald Affeldt and Cyril Cohen.
  Formal foundations of 3D geometry to model robot manipulators.
  In 6th ACM SIGPLAN Conference on Certified Programs and Proofs (CPP 2017),
  Paris, France, January 16--17, 2017, pages 30--42. ACM Press, Jan 2017
  (http://staff.aist.go.jp/reynald.affeldt/documents/robot_cpp_long.pdf).

Some references used in this work:
[murray] Murray, Li, Shankar Sastry: A Mathematical Introduction to Robotic Manipulation;
[springer] Siciliano, Khatib (Eds.): Springer Handbook of Robotics;
[angeles] Angeles: Fundamentals of Robotic Mechanical Systems;
[oneill] O'Neill: Elementary Differential Geometry;
[spong] Spong, Hutchinson, Vidyasagar: Robot Modeling and Control.


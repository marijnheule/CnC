Cube-and-Conquer SAT solver
===========================

This is a repository for Cube-and-Coquer solvers with look-ahead solver
as cube solver. The repository also includes two conquer solvers: 
iglucose (a modification of glucose 3.0) and ilingeling (developed by
Armin Biere).

Installation
============

Build the code using: ./build.sh

This command will compile the solvers march_cu, iglucose (version 3.0), 
and ilingeling (version bjc). 

Cleaning up the repository can simply be done by: ./build.sh clean

Solving
=======

There are two default scripts to solve a benchmarks in the DIMACS format.

./cube-glucose.sh   FILE
./cube-lingeling.sh FILE


Parameters
==========

Both scripts can be extended by the commandline parameters of march:
```
c march_cu help
c USAGE: ./march_cu <input-file> [options]

   where input may be in (uncompressed) DIMACS.

c OPTIONS:

   -h            prints this help message
   -p            plain / no cube mode
   -d <int>      set a static cutoff depth (default:    0, dynamic depth)
   -n <int>      set a static cutoff vars  (default:    0, dynamic depth)
   -e <float>    set a down exponent       (default: 0.30,   fast cubing)
   -f <float>    set a down fraction       (default: 0.02,   fast cubing)
   -l <int>      limit the number of cubes (default:    0,      no limit)
   -s <int>      seed for heuristics       (default:    0,     no random)
   -#            #SAT preprocessing only

c OPTIONAL LOOKAHEAD TECHNIQUES (option will negate the default):

   -gah          global autarky heuristic  (default: on)
   -imp          add both implications     (default: on)
   -wfr          add windfall resolvents   (default: on)

c OUTPUT OPTIONS:

   -o <file>     emit the cubes to <file>  (default: /tmp/cubes.icnf)
   -q            turn on quiet mode        (set default output to stdout)
   -cnf          add the cnf to the cubes

c MAGIC CONSTANTS:

   -bin <float>  binary clause weight      (default:  25.00)
   -dec <float>  size exponential decay    (default:   0.50)
   -min <float>  minimum heuristic value   (default:   8.00)
   -max <float>  maximum heuristic value   (default: 550.00)
   -sli <int>    singlelook iterations     (default:      9)
   -dli <int>    doublelook iterations     (default:      2)
```

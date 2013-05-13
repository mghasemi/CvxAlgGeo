====================
CvxAlgGeo
====================

This package consists of several modules and each module designated to 
perform a specific type of computation that frequently appears in real
algebraic geometry and polynomial optimization.
One can include these modules like this::

    #!/usr/bin/env python

    from CvxAlgGeo import *
    
        OR
    from CvxAlgGeo import semidefinite, geometric, invariant

	
Installation
====================
In Sage -sh mode, simply run 
	
	python setup.py install

Dependencies
====================

The 'semidefinite' module, depends on 'SDP' package for semidefinite 
programming computations. 'SDP' itself requires either 'CvxOpt' or
'cpycsdp' to be installed on Sage.

semidefinite
====================

This module implements semidefinite relaxation method for polynomial 
optimization, introduced by J.B. Lasserre. This module aims to provide 
functionalities that are available for Matlab through 'sostools' or
'GloptiPoly'.

geometric
====================

'geometric' module provides a fast method to approximate a lower bound
for a given polynomial over a given basic closed semialgebraic set using
geometric programming.

invariant
====================

This module provides some experimental computations related to invariant
polynomials.

The latest version of this code is available at:
<https://github.com/mghasemi/pycsdp.git>

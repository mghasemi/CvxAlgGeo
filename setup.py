from distutils.core import setup
from distutils.extension import Extension

Description = "A small Sage package for Polynomial Optimization using \
		tools from real algebraic geometry."

setup(
    name = 'CvxAlgGeo',
    version = '1.0.1',
    author = 'Mehdi Ghasemi',
    author_email = 'mehdi.ghasemi@gmail.com',
    packages = ['CvxAlgGeo'],
    url = 'https://github.com/mghasemi/CvxAlgGeo.git',
    license = 'GNU GNU Public License (GPL)',
    description = Description,
    long_description = open('README.txt').read(),
)

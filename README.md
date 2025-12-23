# ASpirin

ASpirin is an ASProtect unpacker purpose-built for old versions of mushroom game (2005-2008ish).

Its goals are compatibility with modern Windows versions and clean unpacked outputs.

Features:
* Runs on Windows XP ~ Windows 11.
* Clean import call site recovery without introducing another hop.
* Sets correct section names with correct characteristics.
* Bit-perfect recovery of stolen MSVC6 library functions.

Due to the laser focus on these specific targets, applications protected with other versions of ASProtect or built with compilers other than Visual C++ 6.0 are unlikely to work with this.

Thanks go to Piotr Stolarz for his [extensive notes](https://github.com/pstolarz/asprext/tree/master/analysis/1.6x/aip) on ASProtect 1.6x AIP.

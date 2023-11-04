Most of the examples are not tested (or wrong) because i am still rewing the code for bugs and the computation is very slow with regard for the python code.

The code is roughly a translation of what i did in python but now in lean 4.

I tryed to comment on all the part dealing to compute proof term (because at each new finding the hypothesis are rewriten in a new term, wich is bad) but it dit not improved time.

I tryed to comment the part that keeps track of the smalest key to which any object is isomorphic but it did not improved the time.
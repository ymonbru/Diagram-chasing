# Diagram-chasing in double chain complex
The code produced during my internship at the Math Institute of Freiburg (under the supervision of Johan Commelin) for the M1 Hadamard ENS-Paris-Saclay

The goal is to give a double chain complex together with label (zero object, zero map, epi map, mono map , exact pair), and to compute some consequence of these facts.

The algorithm uses a bucn of basic rules (such that a composition of mono is mono, if g°f is mono then f is mono,.....) to propagate information.
The propagation step is done while constructing the data structure,

Then a new graph is made out with the objects and the maps of the salamander lemma (https://ncatlab.org/nlab/show/salamander+lemma)

(and the two graph are compunicating with rules such that if the pair is exact the the homology is a zero object,....)

Once there is nothing more to propagate the results can be displayed, en it's possible to extract a proof from the graph.


For The moment the proof given in output are pen and paper proof (in english) bu future work to be done is to give a text readable by a proof assitant.



In Diagram_chase.ipynb you can find a firendly user notebook.

The file salamander_user.py is there to hide the computation done in the notebook.

Then main the code is in Salamander.py

It uses the file graph_for_salamandre.py to deal with the homology objects of the salamander lemma.
(That one is kind of an adaptation of things i did before in the general case)

In the file Examples-.py you can find some more examples of diagram and the propriety that the algorithm can compute

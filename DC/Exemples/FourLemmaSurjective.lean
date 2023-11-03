import DC.Grid
import DC.Print

-- A->B->C->D
-- |  |  |  |
-- E->F->G->H
-- If the rows are exact, A->E and C -> G is epi, D->H is mono then B->F is epi

--The origin is at 2,2 because of the rescaling to add 0 and ker/coker around
#eval let g:=build [(2,2,"A",false),(2,3,"B",false),(2,4,"C",false),(2,5,"D",false),(3,2,"E",false),(3,3,"F",false),(3,4,"G",false),(3,5,"H",false)]
let g:= add_exact_h g (2,3)
let g:= add_exact_h g (2,4)
let g:= add_exact_h g (3,3)
let g:= add_exact_h g (3,4)
let g:= add_epi_map_grid g (2,2) (3,2)
let g:= add_epi_map_grid g (2,4) (3,4)
let g:= add_mono_map_grid g (2,5) (3,5)
let s:= g.struct.edges[135]?
match s with
  |none => IO.println "the proof is wrong"
  |some s => ProofInEnglish g s.zm.2
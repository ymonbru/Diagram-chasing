import DC.Grid
import DC.Print

--     0     0     0
--     |     |     |
-- 0->A_11->A_12->A_13
--     |     |     |
-- 0->A_21->A_22->A_23
--     |     |     |
-- 0->A_31->A_32->A_13

--If all the rows but the first one and all the columns are exact the the first line is exact

#eval let g:=build [(0,0,"0_00",true),(0,1,"0_01",true),(0,2,"0_02",true),(0,3,"0_03",true),(1,0,"0_10",true),(1,1,"A_11",false),(1,2,"A_12",false),(1,3,"A_13",false),(2,0,"0_20",true),(2,1,"A_21",false),(2,2,"A_22",false),(2,3,"A_13",false),(3,0,"0_30",true),(3,1,"A_31",false),(3,2,"A_32",false),(3,3,"A_33",false)]
let g:=add_exact_h g (2,1)
let g:=add_exact_h g (2,2)
let g:=add_exact_h g (3,1)
let g:=add_exact_h g (3,2)

let g:=add_exact_v g (1,1)
let g:=add_exact_v g (2,2)
let g:=add_exact_v g (3,3)
let g:=add_exact_v g (2,1)
let g:=add_exact_v g (2,2)
let g:=add_exact_v g (2,3)
let g:=add_exact_v g (3,1)
let g:=add_exact_v g (3,2)
let g:=add_exact_v g (3,3)

(g.struct)
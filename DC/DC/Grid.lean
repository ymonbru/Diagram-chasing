/-build a guild structure, able to represent a finite double chain complex. There is the grid as a matrix representing the diagram (and the info of each vertex), a graph structural induced by this matrix, a shadow graph which is induced by the structural graph by taking the homology objects, the extramural and intramural maps from the salamander lemma-/

import DC.GraphForSalamander
import DC.Proof

structure Point where
  key:Nat
  name:String
  i:Int
  j:Int
  dnr: Nat--donnor
  rcpt: Nat--receptor
  vhom: Nat--vertical homology
  hhom: Nat--horizontal homology
deriving Repr

structure Grid where
  pt:Array (Array (Option Point))-- x is in grd[i][j]
  struct:Graph --the graph inducide by the bicomplex
  shadow:Graph --the shadow graph of homology structures
deriving Repr

--a function to add edges on graph, it's there in order to be able to propagate info
def add_edge (g:Graph) (o t:Option Nat): Graph×(Option Nat) :=
  let (g,f):= draw_edge g o t
  (propagate_info_map g f,f)

--some functions to deal with matrix, maybe it exists?
def matrix_modify {a:Type} (g:Array (Array a)) (i j:Nat) (f:a→a):Array (Array a) :=
  Array.modify g i (fun x=> Array.modify x j f)

def get_elem {a:Type} (g:Array (Array (Option a))) (i j:Int):Option a:=
  match i,j with
    |Int.negSucc _ ,_ => none
    |_,Int.negSucc _ => none
    |Int.ofNat i, Int.ofNat j => let gi:=g[i]?
    match gi with
      |none=>none
      |some gi=> let gij:=gi[j]?
    match gij with
      |none=> none
      |some gij=> gij

def matrix_foldl {a b:Type} (f: b→a→b ) (g:b) (m:Array (Array a)):b:=
  Array.foldl (fun init=> fun as=> (Array.foldl f init as)) g m

-- a matrix whose entry (i,j) is (i,j)
def matrix_cord (isize jsize :Nat): Array (Array (Nat×Nat)):=
  let line (i:Nat) : Array (Nat×Nat):=
    let l:=List.range jsize
    let a:= Array.mk l
    Array.map (fun j =>(i,j)) a
  let l:=List.range isize
  let a:=Array.mk l
  let a:= Array.map (fun i => line i) a
  a

mutual

--build a grid guven by a list s of coordinates, names, and bool if zero and gives also the list of keys of coresponding points.
partial def build (l:List (Nat×Nat×String×Bool)):Grid:=
--I need to moove the origin in order to add two rings of zero (and ker-coker) around the diagram.
--(I need to add the same feature for adding propriety over maps)
  match l with
    |[] => {pt:=#[#[]],struct:=g_void,shadow:=g_void}
    |t::q => let max (x:Nat× Nat) (y:Nat×Nat×String×Bool):Nat×Nat:=
    (if x.1<y.1 then y.1 else x.1, if x.2<y.2.1 then y.2.1 else x.2)
    let min (x:Nat× Nat) (y:Nat×Nat×String×Bool):Nat×Nat:=
    (if x.1>y.1 then y.1 else x.1, if x.2>y.2.1 then y.2.1 else x.2)
  let (imax,jmax):=List.foldl max (t.1,t.2.1) q
  let (imin,jmin):=List.foldl min (t.1,t.2.1) q

  let l:=t::q

  let isize:= imax-imin+5--(imax-imin+1)+4for adding ,ker and coker and 0 around
  let jsize:= jmax-jmin+5
  let grid:=({pt:= Array.mkArray isize (Array.mkArray jsize none),struct:=g_void, shadow:=g_void}:Grid)

  let rec change_cord(l:List (Nat×Nat×String×Bool)):(List (Int×Int×String×Bool)):=
    match l with
      |[] => []
      |(xi,xj,sb)::q => (Int.ofNat (xi-imin+2), Int.ofNat (xj-jmin+2),sb)::(change_cord q)

  let l:= change_cord l
--fill the matrix with the information given by the argument, and add the homology objects and the intramural maps
  let build_point (g:Grid) (x:Int×Int×String×Bool):Grid× Option Nat:=
    let p:=get_elem g.pt x.1 x.2.1
    match p with
      |some _ => (g,none)
      |none => match x.1,x.2.1 with
      |Int.negSucc _,_ => (g,none)
      |_,Int.negSucc _ => (g,none)
      |Int.ofNat xi, Int.ofNat xj => match get_elem g.pt xi xj with
        |some p => (g,some p.key)
        |none => if (xi ≥ isize ) ∨ (xj ≥  jsize) then (g,none)
      else let (gst,key):=add_vertex g.struct x.2.2.1
        let (shad,d):=add_vertex g.shadow (s!"donor({x.2.2.1})")
        let (shad,r):=add_vertex shad (s!"receptor({x.2.2.1})")
        let (shad,vh):=add_vertex shad (s!"vHom({x.2.2.1})")
        let (shad,hh):=add_vertex shad (s!"hHom({x.2.2.1})")

        let (shad,_):=add_edge shad r d
        let (shad,_):=add_edge shad r vh
        let (shad,_):=add_edge shad r hh
        let (shad,_):=add_edge shad hh d
        let (shad,_):=add_edge shad vh d

        let p:=({key:=key,name:=x.2.2.1,i:=x.1,j:=x.2.1,dnr:= d,rcpt:= r,vhom:= vh,hhom:= hh}:Point)
        let g:={pt:=matrix_modify g.pt (xi) (xj) (fun _=>p),struct:=gst,shadow:=shad}

        if x.2.2.2 then
          let st:=add_zero_obj g.struct key Proof.Assumption
          let g:={g with struct:=st}
          let g:=propagate_info_vertex g (x.1,x.2.1)
          (g,key)
        else (g,key)
--apply the function build_point to all the point of the matrix
  let process (g:Grid) (x:Int×Int×String×Bool): Grid:=
    let p:= get_elem g.pt x.1 x.2.1
    match p with
    |none => let (g,_):=build_point g x
             g
    |some _ => g-- do not build a point (usefull for corection of stp_h and step_v)
  let grid:=List.foldl process (grid) l

  --connect the edges and add ker and coker at the edges around the diagram
  let connect(g:Grid):Grid:=
    let step_v (g:Grid) (x:Option Point):Grid:=-- disjunction acording to what are the vertex above and under
      match x with
        |none => g
        |some p => let up:=get_elem g.pt (p.i-1) p.j
        let down:=get_elem g.pt (p.i+1) p.j
      match up,down with
        |none,none => g--nothing to do
        |none,some d => let (st,f):=add_edge g.struct p.key d.key--adding the kernel
          match f with
            |none => g
            |some f => let f:=st.edges[f]?
          match f with
            |none => g
            |some f => let g:={g with struct:=st}
          let (g,kerkey):=build_point g (p.i-1,p.j,s!"ker({f.name})",false)
          let (st,_):=add_edge g.struct kerkey p.key
          let g:= {g with struct:=st}

          let g:= add_mono_map_grid g (p.i-1,p.j) (p.i,p.j) (Proof.MapIsMono_IsKer f.key)
          let g:= add_exact_v g (p.i,p.j) (Proof.CompIsExact_KerAndMap)
          g
        |some u,none => let (st,f):=add_edge g.struct u.key p.key-- adding the cokernel
          match f with
            |none => g
            |some f => let f:=st.edges[f]?
          match f with
            |none => g
            |some f => let g:={g with struct:=st}
          let (g,cokerkey):=build_point g (p.i+1,p.j,s!"coker({f.name})",false)
          let (st,_):=add_edge g.struct p.key cokerkey
          let g:={g with struct:=st}

          let g:= add_epi_map_grid g (p.i,p.j) (p.i+1,p.j) (Proof.MapIsEpi_IsCoKer f.key)
          let g:= add_exact_v g (p.i+1,p.j) (Proof.CompIsExact_MapAndCoKer)
          g
        |some u,some d=>let (st,f):=add_edge g.struct p.key d.key-- just connecting
          let (st,e):=add_edge st u.key p.key
          let (st,_):=add_edge st u.key d.key
          let g:={g with struct:=st}
          match e,f with
            |none,_ => g
            |_,none => g
            |some e, some f => let g:=add_zero_map_grid g (p.i-1,p.j) (p.i+1,p.j) (Proof.MapIsZero_VCompInDCC e f)
          g

    let step_h (g:Grid) (x:Option Point):Grid:=--disjunction acording to what are the edges at the right and at the left
      match x with
        |none => g
        |some p =>let left:=get_elem g.pt p.i (p.j-1)
        let right:=get_elem g.pt p.i (p.j+1)
      match left,right with
        |none,none => g
        |none,some r => let (st,f):=add_edge g.struct p.key r.key -- adding the kernel
          match f with
            |none => g
            |some f => let f:=st.edges[f]?
          match f with
            |none => g
            |some f => let g:={g with struct:=st}
          let (g,kerkey):=build_point g (p.i,p.j-1,s!"ker({f.name})",false)
          let (st,_):=add_edge g.struct kerkey p.key
          let g:={g with struct:=st}

          let g:=add_mono_map_grid g (p.i,p.j-1) (p.i,p.j) (Proof.MapIsMono_IsKer f.key)
          let g:=add_exact_h g (p.i,p.j) Proof.CompIsExact_KerAndMap
          g

        |some l,none => let (st,f):=add_edge g.struct l.key p.key -- adding the cokernel
          match f with
            |none => g
            |some f => let f:=st.edges[f]?
          match f with
            |none => g
            |some f => let g:={g with struct:=st}
          let (g,cokerkey):=build_point g (p.i,p.j+1,s!"coker({f.name})",false)
          let (st,_):=add_edge g.struct p.key cokerkey
          let g:={g with struct:=st}

          let g:= add_epi_map_grid g (p.i,p.j) (p.i,p.j+1) (Proof.MapIsEpi_IsCoKer f.key)
          let g:= add_exact_h g (p.i,p.j+1) (Proof.CompIsExact_MapAndCoKer)
          g

        |some l,some r=> let (st,f):=add_edge g.struct p.key r.key -- just connecting
          let (st,e):=add_edge st l.key p.key
          let (st,_):=add_edge st l.key r.key
          let g:={g with struct:= st}
          match e,f with
            |none,_ => g
            |_,none => g
            |some e,some f => let g:=add_zero_map_grid g (p.i,p.j-1) (p.i,p.j+1) (Proof.MapIsZero_HCompInDCC e f)
          g

    let step_d (g:Grid) (x:Option Point):Grid:=-- conecting in diagonal of every square
      match x with
        |none => g
        |some x => let d:=get_elem g.pt (x.i+1) (x.j+1)
      match d with
        |none => g
        |some d => let (st,_):= add_edge g.struct x.key d.key
      let g:={g with struct:=st}
      propagate_info_edge g (x.i,x.j) (x.i+1,x.j+1)

    let salamander_h (g:Grid) (x:Option Point):Grid:=-- add the conclusion of the horizontal salamander lemma into the shadow graph
      match x with
        |none=> g
        |some a=>let b:=get_elem g.pt (a.i) (a.j+1)
      let d:=get_elem g.pt (a.i+1) (a.j+1)
      let c:=get_elem g.pt (a.i-1) (a.j)
      match b,c,d with
        |none,_,_ => g
        |_,none,_ => g
        |_,_,none => g
        |some b,some c,some d => let (shad,f1):= add_edge g.shadow c.dnr a.hhom
      let (shad,f2):= add_edge shad a.hhom a.dnr
      let (shad,f3):= add_edge shad a.dnr b.rcpt
      let (shad,f4):= add_edge shad b.rcpt b.hhom
      let (shad,f5):= add_edge shad b.hhom d.rcpt

      let pf:=(Proof.CompIsExact_HorizontalSalamnder c.key a.key b.key d.key)
      let shad:=add_exact shad f1 f2 pf
      let shad:=add_exact shad f2 f3 pf
      let shad:=add_exact shad f3 f4 pf
      let shad:=add_exact shad f4 f5 pf
      let g:={g with shadow:=shad}

      let g:=propagate_info_shadow g
      g

    let salamander_v (g:Grid) (x:Option Point):Grid:= -- add the conclusion of the vertical salamander lemma into the shadow graph
      match x with
        |none=> g
        |some a=>let b:=get_elem g.pt (a.i+1) (a.j)
      let d:=get_elem g.pt (a.i+1) (a.j+1)
      let c:=get_elem g.pt (a.i) (a.j-1)
      match b,c,d with
        |none,_,_ => g
        |_,none,_ => g
        |_,_,none => g
        |some b,some c,some d => let (shad,f1):= add_edge g.shadow c.dnr a.vhom
      let (shad,f2):= add_edge shad a.vhom a.dnr
      let (shad,f3):= add_edge shad a.dnr b.rcpt
      let (shad,f4):= add_edge shad b.rcpt b.vhom
      let (shad,f5):= add_edge shad b.vhom d.rcpt

      let pf:=(Proof.CompIsExact_VerticalSalamander c.key a.key b.key d.key)
      let shad:=add_exact shad f1 f2 pf
      let shad:=add_exact shad f2 f3 pf
      let shad:=add_exact shad f3 f4 pf
      let shad:=add_exact shad f4 f5 pf
      let g:={g with shadow:=shad}

      let g:=propagate_info_shadow g
      g

    let fill_with_zero (g:Grid) (x:Nat×Nat):Grid:=--add zero where nothing is specified
      let p:=get_elem g.pt x.1 x.2
      match p with
        |some _ => g
        |none => if x.1=0  ∨ (x.1=isize-1) ∨ x.2=0  ∨ (x.2=jsize-1) then
          let (g,_):=build_point g (x.1,x.2,s!"0_({x.1},{x.2})",true)
          g
        else g

    let g:= matrix_foldl fill_with_zero g (matrix_cord isize jsize)
    let g:=matrix_foldl step_v g g.pt

    --add the zeros now in order to avoid problem with adding maps
    let (g,_):=build_point g (1,1,"0_(1,1)",true)
    let (g,_):=build_point g (isize-2,1,s!"0_({isize-2},1)",true)
    let (g,_):=build_point g (1,jsize-2,s!"0_(1,{jsize-2})",true)
    let (g,_):=build_point g (isize-2,jsize-2,s!"0_({isize-2},{jsize-2})",true)

    let g:=matrix_foldl step_h g g.pt
    let g:=matrix_foldl step_v g g.pt

    let g:=matrix_foldl step_d g g.pt
    let g:=matrix_foldl salamander_h g g.pt
    let  g:=matrix_foldl salamander_v g g.pt
    g
  connect grid

partial def add_zero_map_grid (g:Grid) (o:Int×Int) (t:Int×Int) (prf:Statement→Proof:=Proof.Assumption): Grid:=
  let o:=get_elem g.pt o.1 o.2
  let t:=get_elem g.pt t.1 t.2
  match o,t with
    |none,_ => g
    |_,none => g
    |some o,some t => let (st,f):= add_edge g.struct o.key t.key
  let st:= add_zero_map st f prf
  let g:={g with struct:=st}
  propagate_info_edge g (o.i,o.j) (t.i,t.j)

partial def add_mono_map_grid (g:Grid) (o t:Int×Int) (prf:Statement→Proof:=Proof.Assumption) : Grid:=
  let o:=get_elem g.pt o.1 o.2
  let t:=get_elem g.pt t.1 t.2
  match o,t with
    |none,_ => g
    |_,none => g
    |some o,some t => let (st,f):= add_edge g.struct o.key t.key
  let st:= add_mono st f prf
  let g:={g with struct:=st}
  propagate_info_edge g (Int.toNat o.i,Int.toNat o.j) (Int.toNat t.i,Int.toNat t.j)
  --they are supposed to be in nat

partial def add_epi_map_grid (g:Grid) (o t:Int×Int) (prf:Statement→Proof:=Proof.Assumption): Grid:=
  let o:=get_elem g.pt o.1 o.2
  let t:=get_elem g.pt t.1 t.2
  match o,t with
    |none,_ => g
    |_,none => g
    |some o,some t => let (st,f):= add_edge g.struct o.key t.key
  let st:= add_epi st f prf
  let g:={g with struct:=st}
  propagate_info_edge g (o.i,o.j) (t.i,t.j)

partial def add_iso_map_grid (g:Grid) (o t:Nat×Nat) : Grid:=
  let o:=get_elem g.pt o.1 o.2
  let t:=get_elem g.pt t.1 t.2
  match o,t with
    |none,_ => g
    |_,none => g
    |some o,some t => let (st,f):= add_edge g.struct o.key t.key
  let st:= add_iso st f (Proof.Assumption)
  let g:={g with struct:=st}
  propagate_info_edge g (o.i,o.j) (t.i,t.j)

--add the exact condition if it is not yet known, and add the fact that some homolgy object is zero
partial def add_exact_h (g:Grid) (o:Int×Int) (pf:Statement→Proof:= Proof.Assumption):Grid:=
  let p:= get_elem g.pt o.1 o.2
  match p with
    |none => g
    |some p => let left:=get_elem g.pt p.i (p.j-1)
  let right:=get_elem g.pt p.i (p.j+1)
  match left,right with
    |none,_ => g
    |_,none => g
    |some l,some r=> let (st,e):= add_edge g.struct l.key p.key
  let (st,f):= add_edge st p.key r.key

  let test (x:Nat×Nat×Proof):Bool:= (x.1=e)∧(x.2.1=f)
  let se :=Array.find? (g.struct.exact) test
  match se with
  |some _ => g
  |none => let st:=add_exact st e f pf
  let g:={g with struct:=st}
  let shad:=match e,f with
    |none,_ => g.shadow
    |_,none => g.shadow
    |some e, some f => add_zero_obj g.shadow p.hhom (Proof.ObjectIsZero_hHomOfExact (pf (Statement.IsExact e f)))
  let g:={g with shadow:=shad}
  propagate_info_shadow g

partial def add_exact_v (g:Grid) (o:Int×Int) (pf:Statement→Proof:= Proof.Assumption):Grid:=
  let p:= get_elem g.pt o.1 o.2
  match p with
    |none => g
    |some p => let up:=get_elem g.pt (p.i-1) p.j
  let down:=get_elem g.pt (p.i+1) p.j
  match up,down with
    |none,_ => g
    |_,none => g
    |some u,some d=> let (st,e):= add_edge g.struct u.key p.key
  let (st,f):= add_edge st p.key d.key

  let test (x:Nat×Nat×Proof):Bool:= (x.fst=e)∧(x.snd.fst=f)
  let se :=Array.find? (g.struct.exact) test
  match se with
  |some _ => g
  |none => let st:=add_exact st e f pf
  let g:={g with struct:=st}
  let shad:=match e,f with
    |none,_ => g.shadow
    |_,none => g.shadow
    |some e, some f => add_zero_obj g.shadow p.vhom (Proof.ObjectIsZero_vHomOfExact (pf (Statement.IsExact e f)))
  let g:={g with shadow:=shad}
  propagate_info_shadow g

--check for every rule where "f is..." can be an hypothesis if it now apply and the add the consequence to the grid.
partial def propagate_info_edge (g:Grid) (o t:Int×Int):Grid:=
  let o:= get_elem g.pt o.1 o.2
  let t:= get_elem g.pt t.1 t.2
  match o,t with
    |none,_ => g
    |_,none => g
    |some o,some t => let (st,f):= add_edge g.struct o.key t.key
  match f with
    |none => g
    |some f => let f:=st.edges[f]?
    match f with
      |none => g
      |some f => let test (g:Grid):Grid:=
    if f.zm.1 then
      let (shad,f_extramural):= add_edge g.shadow o.dnr t.rcpt
      let shad:=add_zero_map shad f_extramural (Proof.MapIsZero_ExtramuralOfZero f.zm.2)
      {g with shadow:=shad}
    else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j+1 ∧ f.epi.1 then
        let r:= g.shadow.vertex[t.rcpt]?
        match r with
          |none => g
          |some r => if r.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow r.key (Proof.ObjectIsZero_ReceptorOfCoDomainOfDiagEpi f.epi.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j+1 ∧ f.mono.1 then
        let d:= g.shadow.vertex[o.dnr]?
        match d with
          |none => g
          |some d => if d.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow d.key (Proof.ObjectIsZero_DonorOfDomainOfDiagMono f.mono.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i ∧ t.j=o.j+1 ∧ f.mono.1 then
        let r:= g.shadow.vertex[o.rcpt]?
        match r with
          |none => g
          |some r => if r.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow r.key (Proof.ObjectIsZero_ReceptorOfDomainOfHorizMono f.mono.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i ∧ t.j=o.j+1 ∧ f.mono.1 then
        let hh:= g.shadow.vertex[o.hhom]?
        match hh with
          |none => g
          |some hh => if hh.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow hh.key (Proof.ObjectIsZero_hHomOfDomainOfHorizMono f.mono.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i ∧ t.j=o.j+1 ∧ f.epi.1 then
        let d:= g.shadow.vertex[o.dnr]?
        match d with
          |none => g
          |some d => if d.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow d.key (Proof.ObjectIsZero_DonorOfDomainOfHorizEpi f.epi.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i ∧ t.j=o.j+1 ∧ f.epi.1 then
        let hh:= g.shadow.vertex[o.hhom]?
        match hh with
          |none => g
          |some hh => if hh.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow hh.key (Proof.ObjectIsZero_hHomOfDomainOfHorizEpi f.epi.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j ∧ f.mono.1 then
        let r:= g.shadow.vertex[o.rcpt]?
        match r with
          |none => g
          |some r => if r.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow r.key (Proof.ObjectIsZero_ReceptorOfDomainOfVerticMono f.mono.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j ∧ f.mono.1 then
        let vh:= g.shadow.vertex[o.vhom]?
        match vh with
          |none => g
          |some vh => if vh.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow vh.key (Proof.ObjectIsZero_vHomOfVerticMono f.mono.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j ∧ f.epi.1 then
        let d:= g.shadow.vertex[t.dnr]?
        match d with
          |none => g
          |some d => if d.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow d.key (Proof.ObjectIsZero_DonorOfCoDomainOfVerticEpi f.epi.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid):Grid:=
      if t.i=o.i+1 ∧ t.j=o.j ∧ f.epi.1 then
        let vh:= g.shadow.vertex[t.vhom]?
        match vh with
          |none => g
          |some vh => if vh.zo.1 then g
          else
          let shad:= add_zero_obj g.shadow vh.key (Proof.ObjectIsZero_vHomOfVerticEpi f.epi.2)
          {g with shadow:=shad}
      else g
    let g:=test g

    let test (g:Grid): Grid :=
      if t.i=o.i+1 ∧ t.j=o.j then
        match get_elem g.pt (o.i-1) o.j with
          |none => g
          |some s => let e:= Array.find? (g.struct.edges) (fun x=> (x.o=s.key)∧(x.t=o.key))
        match e with
          |none => g
          |some e => let ex := Array.find? (g.struct.exact) (fun x=> (x.1=e.key)∧(x.2.1=f.key))
        match ex with
          |none => g
          |some ex => let shad := add_zero_obj g.shadow o.vhom (Proof.ObjectIsZero_vHomOfExact ex.2.2)
        {g with shadow:= shad}
      else g
    let g:= test g

    let test (g:Grid): Grid :=
      if t.i=o.i+1 ∧ t.j=o.j then
        match get_elem g.pt (t.i+1) t.j with
          |none => g
          |some s => let h:= Array.find? (g.struct.edges) (fun x=> (x.o=t.key)∧(x.t=s.key))
        match h with
          |none => g
          |some h => let ex := Array.find? (g.struct.exact) (fun x=> (x.1=f.key)∧(x.2.1=h.key))
        match ex with
          |none => g
          |some ex => let shad := add_zero_obj g.shadow t.vhom (Proof.ObjectIsZero_vHomOfExact ex.2.2)
        {g with shadow:= shad}
      else g
    let g:= test g

    let test (g:Grid): Grid :=
      if t.i=o.i ∧ t.j=o.j+1 then
        match get_elem g.pt o.i (o.j-1) with
          |none => g
          |some s => let e:= Array.find? (g.struct.edges) (fun x=> (x.o=s.key)∧(x.t=o.key))
        match e with
          |none => g
          |some e => let ex := Array.find? (g.struct.exact) (fun x=> (x.1=e.key)∧(x.2.1=f.key))
        match ex with
          |none => g
          |some ex => let shad := add_zero_obj g.shadow o.vhom (Proof.ObjectIsZero_hHomOfExact ex.2.2)
        {g with shadow:= shad}
      else g
    let g:= test g

    let test (g:Grid): Grid :=
      if t.i=o.i ∧ t.j=o.j+1 then
        match get_elem g.pt t.i (t.j+1) with
          |none => g
          |some s => let h:= Array.find? (g.struct.edges) (fun x=> (x.o=t.key)∧(x.t=s.key))
        match h with
          |none => g
          |some h => let ex := Array.find? (g.struct.exact) (fun x=> (x.1=f.key)∧(x.2.1=h.key))
        match ex with
          |none => g
          |some ex => let shad := add_zero_obj g.shadow t.vhom (Proof.ObjectIsZero_hHomOfExact ex.2.2)
        {g with shadow:= shad}
      else g

    let g:= test g
    let g:= propagate_info_vertex g (o.i,o.j)
    let g:=propagate_info_vertex g (t.i,t.j)
    propagate_info_shadow g

--same than before but for vertices
partial def propagate_info_vertex (g:Grid) (p:Int×Int):Grid:=
  let p:=get_elem g.pt p.1 p.2
  match p with
    |none => g
    |some p => let x:= g.struct.vertex[p.key]?
  match x with
    |none => g
    |some x => if x.zo.1 then
    let shad:= add_zero_obj g.shadow (p.dnr) (Proof.ObjectIsZero_DonnorOfZero x.zo.2)
    let shad:= add_zero_obj shad (p.rcpt) (Proof.ObjectIsZero_ReceptorOfZero x.zo.2)
    let shad:= add_zero_obj shad (p.hhom) (Proof.ObjectIsZero_hHomOfZero x.zo.2)
    let shad:= add_zero_obj shad (p.vhom) (Proof.ObjectIsZero_vHomOfZero x.zo.2)
    let g:={g with shadow:=shad}
    propagate_info_shadow g
    else g

--same than before but for the shadow graph
partial def propagate_info_shadow (g:Grid):Grid:=
  let test_h (g:Grid) (p:Option Point): Grid:=
    match p with
      |none => g
      |some p => let hhom:= g.shadow.vertex[p.hhom]?
    match hhom with
      |none => g
      |some hhom => if hhom.zo.1 then add_exact_h g (p.i,p.j) (Proof.CompIsExact_hHomIsZero hhom.zo.2)
      else g
  let test_v (g:Grid) (p:Option Point): Grid:=
    match p with
      |none => g
      |some p => let vhom:= g.shadow.vertex[p.vhom]?
    match vhom with
      |none => g
      |some vhom => if vhom.zo.1 then add_exact_v g (p.i, p.j) (Proof.CompIsExact_vHomIsZero vhom.zo.2)
      else g
  let g:=matrix_foldl test_h g g.pt
  let g:=matrix_foldl test_v g g.pt
  g


end--mutual


--useful for some test, in order to just get the marix with the names from a grid
def filtre (g:Grid):Array (Array String):=
  let f (p:Option Point): String:=
    match p with
      |none=>""
      |some p=> p.name
  Array.map (fun a=> Array.map f a) g.pt

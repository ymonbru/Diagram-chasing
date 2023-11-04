/- The goal is to define a structure of graph, and tools to deal with it in the next files-/
import DC.Proof

structure edge where
  key:Nat
  name:String
  o:Nat--key of the origin
  t:Nat--key of the tail
  zm:Bool×Proof--is a zero map?
  mono:Bool×Proof--is a mono map?
  epi:Bool×Proof--is an epi map?
  iso:Bool×Proof
deriving Repr

/-Iso ref is in order to give proof of existence of conection morphisms-/
structure vertex where
  key:Nat
  name:String
  zo:Bool×Proof--is a zero object
  iso_ref:Nat×Proof-- the smalest key to which it is isomorphic
deriving Repr

structure Graph where
  edges: Array edge
  vertex: Array vertex
  exact: Array (Nat×Nat×Proof)-- list of exacts compositions
deriving Repr

def numb_v (g:Graph):Nat:=Array.size (g.vertex)--number of vertices

def numb_e (g:Graph):Nat:=Array.size (g.edges)--number of edges

def g_void:Graph:={edges:=#[], vertex:=#[],exact:=#[]}-- graph with no vertex and no edge


def add_vertex (g:Graph) (name:String):Graph × Nat:=--add a vertex to a given graph
  let nv:= numb_v g
  let pfvoid:=Proof.Assumption Statement.Nothing
  let newv:=({key:=nv,name:=name,zo:=(false,pfvoid), iso_ref:=(nv,Proof.ObjectsAreIso_IsoItself (Statement.AreIsoObj nv nv))}:vertex)
  let newg:={g with vertex:=g.vertex.push newv}
  (newg,nv)

def draw_edge (g:Graph) (o t: Option Nat):Graph × (Option Nat):=--add an edge to a given graph and propagate the information of edge representing zero morphism and vertex representing zero object.
  match o,t with
    |none,_ => (g,none)
    |_,none => (g,none)
    |some o,some t=>let o:=g.vertex[o]?
  let t:=g.vertex[t]?
  match o,t with
    |none,_=>(g,none)
    |_,none=> (g,none)
    |some o,some t=> let ne:= numb_e g
  let test (e:edge):Bool:= (e.o=o.key)∧(e.t=t.key)
  let se :=Array.find? (g.edges) test
  match se with
    |none=> let b:=(false,Proof.Assumption Statement.Nothing)
            let zm := (if o.zo.1 then (true,Proof.MapIsZero_DomainIsZero o.zo.2 (Statement.IsZeroMap ne))
            else if t.zo.1 then (true,Proof.MapIsZero_CoDomainIsZero t.zo.2 (Statement.IsZeroMap ne))
            else (false,Proof.Assumption Statement.Nothing))
            let s:= (s! "f{ne} : {o.name} -> {t.name}")
            let newe:= ({key:=ne, name:=s,o:=o.key,t:=t.key,zm:=zm,mono:=b,epi:=b,iso:=b}:edge)
            ({g with edges:=g.edges.push newe},ne)
    |some e => (g,e.key)

--list of edges whose start point is x
def domain_is_x (g:Graph) (x:Nat):List Nat:=
  let f (l:List Nat) (e:edge):List Nat:=
    if e.o=x then
    (e.key)::l
    else l
  Array.foldl f [] g.edges

--list of edges whose end point is x
def codomain_is_x (g:Graph) (x:Nat):List Nat:=
  let f (l:List Nat) (e:edge):List Nat:=
    if e.t=x then
    (e.key)::l
    else l
  Array.foldl f [] g.edges

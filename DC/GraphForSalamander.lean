/-Same than in the file Graph, but adding the possibility to compute things abour mono-epi map... and so on -/
import DC.Proof
import DC.Graph

mutual

partial def add_zero_obj (g:Graph) (x:Option Nat) (p:Statement→Proof): Graph:=
  match x with
    |none => g
    |some x => let x:=g.vertex[x]?
  match x with
  |none=> g
  |some x=> if x.zo.1 then g
  else
  let prf:=p (Statement.IsZeroObj x.key)
  let newv:=(g.vertex).modify x.key (fun y=>{y with zo:=(true,prf)})
  let g:= {g with vertex:=newv}
  let dom:= domain_is_x g (x.key)
  let cdom:=codomain_is_x g (x.key)

  let mapiszero_domainiszero (gr:Graph) (e:Nat):Graph:=
    let gr:=add_zero_map gr e (Proof.MapIsZero_DomainIsZero prf)
    propagate_info_map gr e

  let mapismono_domainiszero (gr:Graph) (e:Nat):Graph:=
    let gr:=add_mono gr e (Proof.MapIsMono_DomainIsZero prf)
    propagate_info_map gr e

  let mapiszero_cdomainiszero (gr:Graph) (e:Nat):Graph:=
    let gr:=add_zero_map gr e (Proof.MapIsZero_CoDomainIsZero prf)
    let gr:=add_epi gr e (Proof.MapIsEpi_CoDomainIsZero prf)
    propagate_info_map gr e

  let mapisepi_cdomainiszero (gr:Graph) (e:Nat):Graph:=
    let gr:=add_zero_map gr e (Proof.MapIsZero_CoDomainIsZero prf)
    let gr:=add_epi gr e (Proof.MapIsEpi_CoDomainIsZero prf)
    propagate_info_map gr e

  --The treatment of dom and cdom is not done in one function in order to get simpler proof in the end
  let g:=List.foldl mapiszero_domainiszero g dom
  let g:=List.foldl mapiszero_cdomainiszero g cdom
  let g:=List.foldl mapismono_domainiszero g dom
  List.foldl mapisepi_cdomainiszero g cdom

partial def add_epi (g:Graph) (e:Option Nat) (p:Statement→Proof):Graph:=
  match e with
  |none=> g
  |some e=>
  let e:=g.edges[e]?
  match e with
  |none=> g
  |some e=> if e.epi.1 then g
  else
  let newe:= {e with epi:=(true,p (Statement.IsEpiMap e.key))}
  let neweg:=(g.edges).modify e.key (fun _=>newe)
  let g:={g with edges:=neweg}
  propagate_info_map g e.key

partial def add_mono (g:Graph) (e:Option Nat) (p:Statement→ Proof):Graph:=
  match e with
  |none=> g
  |some e=>
  let e:=g.edges[e]?
  match e with
  |none=> g
  |some e=>  if e.mono.1 then g
  else
  let newe:= ({e with mono:=(true,p (Statement.IsMonoMap e.key))})
  let neweg:=(g.edges).modify e.key (fun _=>newe)
  let g:={g with edges:=neweg}
  propagate_info_map g e.key

partial def add_iso (g:Graph) (e:Option Nat) (p:Statement→ Proof):Graph:=
  match e with
  |none=> g
  |some e=>
  let e:=g.edges[e]?
  match e with
  |none=> g
  |some e=>if e.iso.1 then g
  else
  let pf:=p (Statement.IsIsoMap e.key)
  let newe:= {e with iso:=(true,pf)}
  let neweg:=(g.edges).modify e.key (fun _=>newe)
  let g:={g with edges:=neweg}

  /-I tried to comment this part but it dit not improved the time of computation, it's to have a tool to test if two objects are isomorphic by remebering the smalest key to which it's isomorphic -/
  let rec update_iso_ref (x y:Nat) (v:vertex):vertex:=
    if x<y then update_iso_ref y x v
    else
    let old_ref:=v.iso_ref.1
    if old_ref=x then
      let y:=g.vertex[y]?
      match y with
        |none=> v
        |some y=> let new_ref:= y.iso_ref.1
      {v with iso_ref:=(new_ref, Proof.ObjectsAreIso_IsoTrans y.iso_ref.2 pf (Statement.AreIsoObj v.key new_ref))}
    else v
  let g:={g with vertex:=Array.map (update_iso_ref e.o e.t) g.vertex}
  propagate_info_map g e.key

partial def add_zero_map (g:Graph) (e:Option Nat) (p:Statement→ Proof):Graph:=
  match e with
  |none=> g
  |some e=>
  let e:=g.edges[e]?
  match e with
  |none=> g
  |some e=>  if e.zm.1 then g
  else
  let newe:= ({e with zm:=(true,p (Statement.IsZeroMap e.key))}:edge)
  let neweg:=(g.edges).modify e.key (fun _=>newe)
  let g:={g with edges:=neweg}
  propagate_info_map g e.key

--add e°f as an exact composition if it is possible, and add the edge of composition
partial def add_exact (g:Graph) (e f:Option Nat) (p:Statement→ Proof):Graph:=
  match e,f with
  |_,none=> g
  |none,_=>g
  |some e,some f=>
  let e:=g.edges[e]?
  let f:=g.edges[f]?
  match e,f with
  |none,_=>g
  |_,none=>g
  |some e,some f=>
  if not (f.o=e.t) then g
  else
  let test (x:Nat×Nat×Proof):Bool:= (x.fst=e.key)∧(x.snd.fst=f.key)
  let se :=Array.find? (g.exact) test
  match se with
    |none=> let pf:= p (Statement.IsExact e.key f.key)
            let newex:= (e.key,f.key,pf)
            let newg:={g with exact:=g.exact.push newex}
            let (newg,ne):=draw_edge newg e.o f.t
            match ne with
            |none=> newg
            |some ne=>
            add_zero_map newg ne (Proof.MapIsZero_ExactComp  pf)
    |some _ => g

--test the possible consequences of a new finding
partial def propagate_info_map (g:Graph) (f: Option Nat):Graph:=
  match f with
    |none => g
    |some f => let f:=g.edges[f]?
  match f with
  |none=> g
  |some f=>

  let test (gr:Graph) (f:edge):Graph:=
    let o:=gr.vertex[f.o]?
    match o with
      |none=> gr
      |some o=> if (o.zo.1 ∧ (not f.zm.1)) then
    add_zero_map  gr f.key (Proof.MapIsZero_DomainIsZero o.zo.2)
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    let t:=gr.vertex[f.t]?
    match t with
      |none=> gr
      |some t=> if (t.zo.1 ∧ (not f.zm.1)) then
    add_zero_map  gr f.key (Proof.MapIsZero_CoDomainIsZero t.zo.2)
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    let o:=gr.vertex[f.o]?
    match o with
    |none => gr
    |some o =>
    if ( o.zo.1 ∧ (not f.mono.1)) then
      add_mono gr f.key (Proof.MapIsMono_DomainIsZero o.zo.2)
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    let t:=gr.vertex[f.t]?
    match t with
    |none => gr
    |some t =>
    if ( t.zo.1 ∧ (not f.epi.1)) then
      add_epi gr f.key (Proof.MapIsEpi_CoDomainIsZero t.zo.2)
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    let t:=gr.vertex[f.t]?
    match t with
    |none=> gr
    |some t=>
    if (f.epi.1 ∧ f.zm.1 ∧ (not t.zo.1)) then
      add_zero_obj gr t.key (Proof.ObjectIsZero_CoDomainOfEpiZero (f.epi.2) (f.zm.2))
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    let o:=gr.vertex[f.o]?
    match o with
    |none=> gr
    |some o=>
    if ( f.mono.1 ∧ f.zm.1 ∧ (not o.zo.1)) then
      add_zero_obj gr o.key (Proof.ObjectIsZero_DomainOfMonoZero (f.mono.2) (f.zm.2))
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    if (f.mono.1 ∧ f.epi.1 ∧ (not f.iso.1)) then
      add_iso gr f.key (Proof.MapIsIso_MonoAndEpiMap f.mono.2 f.epi.2)
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    if (f.iso.1 ∧ (not f.mono.1))then
      add_mono gr f.key (Proof.MapIsMono_IsIso (f.iso.2))
    else gr
  let g:= test g f

  let test (gr:Graph) (f:edge):Graph:=
    if (f.iso.1 ∧ (not f.epi.1))then
      add_epi gr f.key (Proof.MapIsEpi_IsIso (f.iso.2))
    else gr
  let g:= test g f

  let trig1 (g:Graph) (e:edge):Graph:=
    if e.o=f.o then
      let se :=Array.find? (g.edges) (fun x=> (x.o=f.t)∧(x.t=e.t))
      match se with
        |none=> let se :=Array.find? (g.edges) (fun x=> (x.o=e.t)∧(x.t=f.t))
                match se with
                  |none=> g
                  |some se=> propagate_info_trgl g e.key se.key f.key
        |some se=>propagate_info_trgl g f.key se.key e.key
    else g

  let g:= Array.foldl (trig1) g g.edges

  let trig2 (g:Graph) (e:edge):Graph:=
    if e.t=f.t then
      let se :=Array.find? (g.edges) (fun x=> (x.o=f.o)∧(x.t=e.o))
      match se with
        |none=> let se :=Array.find? (g.edges) (fun x=> (x.o=e.o)∧(x.t=f.o))
                match se with
                  |none=> g
                  |some se=> propagate_info_trgl g se.key f.key e.key
        |some se=>propagate_info_trgl g se.key e.key f.key
    else g

  let g:= Array.foldl (trig2) g g.edges
  g

-- c=b°a

--If a test succed then the other test are not done but the will be during the recurcive call the follows from the adding of information, it avoid to update a,b and c at each step
partial def propagate_info_trgl (g:Graph) (a b c:Option Nat):Graph:=
  match a,b,c with
    |none,_,_=> g
    |_,none,_=> g
    |_,_,none=> g
    |some a,some b, some c=>
    let a:=g.edges[a]?
    let b:=g.edges[b]?
    let c:=g.edges[c]?
  match a,b,c with
    |none,_,_=> g
    |_,none,_=> g
    |_,_,none=> g
    |some a,some b, some c=>
    if (a.o=c.o ∧  a.t=b.o ∧ b.t=c.t) then

    if a.zm.1 ∧ (not c.zm.1)  then
      add_zero_map g c.key (Proof.MapIsZero_PreCompByZero a.zm.2 a.key)
    else
    if b.zm.1 ∧ (not c.zm.1)  then
      add_zero_map g c.key (Proof.MapIsZero_PostCompByZero a.key b.zm.2)
    else
    if c.zm.1 ∧ b.mono.1 ∧ (not a.zm.1)  then
      add_zero_map g a.key (Proof.MapIsZero_PosCompByMonoIsZero b.mono.2 c.zm.2)
    else
    if c.zm.1 ∧ a.epi.1 ∧ (not b.zm.1)  then
      add_zero_map g b.key (Proof.MapIsZero_PreCompByEpiIsZero a.epi.2 c.zm.2)
    else
    if a.mono.1 ∧ b.mono.1 ∧ (not c.mono.1)  then
      add_mono g c.key (Proof.MapIsMono_CompOfMono a.mono.2 b.mono.2)
    else
    if c.mono.1 ∧ (not a.mono.1)  then
      add_mono g a.key (Proof.MapIsMono_PostCompIsMono b.key c.mono.2)
    else
    if a.epi.1 ∧ b.epi.1 ∧ (not c.epi.1)  then
      add_epi g c.key (Proof.MapIsEpi_CompOfEpi a.epi.2 b.epi.2)
    else
    if c.epi.1 ∧ (not b.epi.1)  then
      add_epi g b.key (Proof.MapIsEpi_PreCompIsEpi a.key c.epi.2)
    else

    if c.zm.1 then -- if not the b°a is not exact
    let ex:=Array.find? g.exact (fun x=> x.1=a.key∧x.2.1=b.key )
    match ex with
    |none =>
    if a.zm.1 ∧ b.mono.1 then
      add_exact g a.key b.key (Proof.CompIsExact_ZeroWithMono a.zm.2 b.mono.2)
    else
    if a.epi.1 ∧ b.zm.1 then
      add_exact g a.key b.key (Proof.CompIsExact_EpiWithZero a.epi.2 b.zm.2)
    else
      g
    |some ex =>
    if b.mono.1 ∧ (not a.zm.1) then
      add_zero_map g a.key (Proof.MapIsZero_ExactMonoWithMap ex.2.2 b.mono.2)
    else
    if a.epi.1 ∧ (not b.zm.1) then
      add_zero_map g b.key (Proof.MapIsZero_ExactMapWithEpi ex.2.2 a.epi.2)
    else
    if a.zm.1 ∧ (not b.mono.1) then
      add_mono g b.key (Proof.MapIsMono_ExactMapWithZero ex.2.2 a.zm.2)
    else
    if b.zm.1 ∧ (not a.epi.1) then
      add_epi g a.key (Proof.MapIsEpi_ExactZeroWithMap ex.2.2 b.zm.2)
    else g
    else g
    else g

end--of mutual bloc

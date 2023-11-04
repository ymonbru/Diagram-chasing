/- The goal is to have something to make a proof term (from the file Proof) readable in english, (and to work through testing).
In case of problem it return "The proof is wrong x", the x is to be able to find the origin of the mistake-/

import DC.Proof
import DC.Grid

def line: IO Unit :=
  IO.println ""

def StatementOfProof (p:Proof):Statement:=
  match p with
  |Proof.Assumption s => s
  |Proof.MapIsZero_DomainIsZero _ s => s
  |Proof.MapIsZero_CoDomainIsZero _ s => s
  |Proof.MapIsZero_PreCompByZero _ _ s => s
  |Proof.MapIsZero_PostCompByZero _ _ s => s
  |Proof.MapIsZero_ExactComp  _ s => s
  |Proof.MapIsZero_HCompInDCC _ _ s => s
  |Proof.MapIsZero_VCompInDCC _ _ s => s
  |Proof.MapIsZero_PosCompByMonoIsZero _ _ s => s
  |Proof.MapIsZero_PreCompByEpiIsZero _ _ s => s
  |Proof.MapIsZero_ExactMonoWithMap _ _ s => s
  |Proof.MapIsZero_ExactMapWithEpi _ _ s => s
  |Proof.MapIsZero_ExtramuralOfZero _ s => s
  |Proof.MapIsMono_IsKer _ s => s
  |Proof.MapIsMono_IsIso _ s => s
  |Proof.MapIsMono_CompOfMono _ _ s => s
  |Proof.MapIsMono_PostCompIsMono _ _ s => s
  |Proof.MapIsMono_ExactMapWithZero _ _ s => s
  |Proof.MapIsMono_DomainIsZero _ s => s
  |Proof.MapIsEpi_IsCoKer _ s => s
  |Proof.MapIsEpi_IsIso _ s => s
  |Proof.MapIsEpi_CompOfEpi _ _ s => s
  |Proof.MapIsEpi_PreCompIsEpi _ _ s => s
  |Proof.MapIsEpi_ExactZeroWithMap _ _ s => s
  |Proof.MapIsEpi_CoDomainIsZero _ s => s
  |Proof.MapIsIso_MonoAndEpiMap _ _ s => s
  |Proof.ObjectIsZero_DomainOfMonoZero _ _ s => s
  |Proof.ObjectIsZero_CoDomainOfEpiZero _ _ s => s
  |Proof.ObjectIsZero_DonnorOfZero _ s => s
  |Proof.ObjectIsZero_DonorOfDomainOfDiagMono _ s => s
  |Proof.ObjectIsZero_DonorOfDomainOfHorizEpi _ s => s
  |Proof.ObjectIsZero_DonorOfCoDomainOfVerticEpi _ s => s
  |Proof.ObjectIsZero_ReceptorOfZero _ s => s
  |Proof.ObjectIsZero_ReceptorOfCoDomainOfDiagEpi _ s => s
  |Proof.ObjectIsZero_ReceptorOfDomainOfHorizMono _ s => s
  |Proof.ObjectIsZero_ReceptorOfDomainOfVerticMono _ s => s
  |Proof.ObjectIsZero_hHomOfZero _ s => s
  |Proof.ObjectIsZero_hHomOfExact _ s => s
  |Proof.ObjectIsZero_hHomOfDomainOfHorizEpi _ s => s
  |Proof.ObjectIsZero_hHomOfDomainOfHorizMono _ s => s
  |Proof.ObjectIsZero_vHomOfZero _ s => s
  |Proof.ObjectIsZero_vHomOfExact _ s => s
  |Proof.ObjectIsZero_vHomOfVerticMono _ s => s
  |Proof.ObjectIsZero_vHomOfVerticEpi _ s => s
  |Proof.ObjectsAreIso_IsoItself s => s
  |Proof.ObjectsAreIso_IsoTrans _ _ s => s
  |Proof.CompIsExact_KerAndMap s => s
  |Proof.CompIsExact_MapAndCoKer s => s
  |Proof.CompIsExact_ZeroWithMono _ _ s => s
  |Proof.CompIsExact_EpiWithZero _ _ s => s
  |Proof.CompIsExact_hHomIsZero _ s => s
  |Proof.CompIsExact_vHomIsZero _ s => s
  |Proof.CompIsExact_HorizontalSalamnder _ _ _ _ s => s
  |Proof.CompIsExact_VerticalSalamander _ _ _ _ s => s

--It does not work if the proof is originaly from the shadow graph (but its not needed). The aff_statement is in order to keep track of the graph curently explored (the normal or the shadow)
def ProofInEnglish (gr:Grid) (p:Proof):IO Unit:=
  let aff_statement (g:Graph) (s:Statement): String :=
    match s with
      |Statement.Nothing => "Nothing"
      |Statement.IsZeroMap n => let f:= g.edges[n]?
        match f with
          |none => "The proof is wrong 1"
          |some f => s!"The map {f.name} is zero"
      |Statement.IsZeroObj n => let o:= g.vertex[n]?
        match o with
          |none => "The proof is wrong 2"
          |some o => s!"The object {o.name} is zero"
      |Statement.IsMonoMap n => let f:= g.edges[n]?
        match f with
         |none => "The proof is wrong 3"
         |some f => s!"Th map {f.name} is a monomorphism"
      |Statement.IsEpiMap n => let f:= g.edges[n]?
        match f with
         |none => "The proof is wrong 4"
         |some f => s!"Th map {f.name} is an epimorphism"
      |Statement.IsIsoMap n => let f:= g.edges[n]?
        match f with
         |none => "The proof is wrong 5"
         |some f => s!"Th map {f.name} is an isomorphism"
      |Statement.IsExact m n => let f:= g.edges[m]?
        let e:=g.edges[n]?
        match e,f with
         |none,_ => "The proof is wrong 6"
         |_,none => "The proof is wrong 7"
         |some e,some f => s!"The composition of {e.name} with {f.name} is exact"
      |Statement.AreIsoObj n m=> let x:= g.edges[m]?
        let y:=g.edges[n]?
        match x,y with
         |none,_ => "The proof is wrong 8"
         |_,none => "The proof is wrong 9"
         |some x,some y => s!"The object {x.name} is isomorphic to the object {y.name}"

  let name_st (s:Statement):String :=
    aff_statement gr.struct s
  let name_shad (s:Statement):String :=
    aff_statement gr.shadow s

-- n°m=nm
-- It's just a case disjoinctions about all the possible arguments and a translation in english
  let rec aff_proof (g:Graph) (name: Statement→String) (pf:Proof):IO Unit:=
    match pf with
      |Proof.Assumption s => IO.println (s!"{name s} by assumption ")
      |Proof.MapIsZero_DomainIsZero p s => do aff_proof g name p;line; IO.println (s!"{name s} because it's domain is zero")

      |Proof.MapIsZero_CoDomainIsZero p s => do aff_proof g name p;line; IO.println (s!"{name s} because it's codomain is zero")

      |Proof.MapIsZero_PreCompByZero p n s => match StatementOfProof p with
        |Statement.IsZeroMap m => let m:= g.edges[m]?
          let n:=g.edges[n]?
          match m,n with
            |none,_ => IO.println "The proof is wrong 10"
            |_,none => IO.println "The proof is wrong 11"
            |some n,some m => do aff_proof g name p;line; IO.println (s!"{name s} because it's equal to {n.name} composed with {m.name} and {m.name} is a zero map")
        |_ => IO.println "The proof is wrong 12"

      |Proof.MapIsZero_PostCompByZero m p s => match StatementOfProof p with
        |Statement.IsZeroMap n => let n:= g.edges[n]?
          let m:=g.edges[m]?
          match n,m with
            |none,_ => IO.println "The proof is wrong 13"
            |_,none => IO.println "The proof is wrong 14"
            |some n,some m => do aff_proof g name p;line; IO.println (s!"{name s} because it's equal to {n.name} composed with {m.name} and {n.name} is a zero map")
        |_ => IO.println "The proof is wrong 15"

      |Proof.MapIsZero_ExactComp p s => match StatementOfProof p with
        |Statement.IsExact e f => let e:=g.edges[e]?
            let f:=g.edges[f]?
            match e,f with
              |none,_ => IO.println "The proof is wrong 16"
              |_,none => IO.println "The proof is wrong 17"
              |some e,some f => do aff_proof g name p;line; IO.println (s!"{name s} because it's equal to {f.name} composed with {e.name} and the composition is exact")
        |_ => IO.println "The proof is wrong 18"

      |Proof.MapIsZero_HCompInDCC n m s => let n:=g.edges[n]?
            let m:=g.edges[m]?
            match n,m with
              |none,_ => IO.println "The proof is wrong 19"
              |_,none => IO.println "The proof is wrong 20"
              |some n, some m => IO.println (s!"{name s} because it's equal to {n.name} composed with {m.name} and the composition is horizontal in the DCC")

      |Proof.MapIsZero_VCompInDCC n m s => let n:=g.edges[n]?
            let m:=g.edges[m]?
            match n,m with
              |none,_ => IO.println "The proof is wrong 21"
              |_,none => IO.println "The proof is wrong 22"
              |some n, some m => IO.println (s!"{name s} because it's equal to {n.name} composed with {m.name} and the composition is vertical in the DCC")

      |Proof.MapIsZero_PosCompByMonoIsZero pm pz s => match StatementOfProof pm,StatementOfProof pz with
        |Statement.IsMonoMap n,Statement.IsZeroMap nm => let n:=g.edges[n]?
            let nm:=g.edges[nm]?
            match n,nm with
              |none,_ => IO.println "The proof is wrong 23"
              |_,none => IO.println "The proof is wrong 24"
              |some n, some nm => do aff_proof g name pm; line; do aff_proof g name pz; line; IO.println (s!"{name s} because post-composed by the mono {n.name} the map is  {nm.name} which is zero")
        |_,_ => IO.println "The proof is wrong 25"

      |Proof.MapIsZero_PreCompByEpiIsZero pe pz s => match StatementOfProof pe,StatementOfProof pz with
        |Statement.IsEpiMap m,Statement.IsZeroMap nm => let m:=g.edges[m]?
            let nm:=g.edges[nm]?
            match m,nm with
              |none,_ => IO.println "The proof is wrong 26"
              |_,none => IO.println "The proof is wrong 27"
              |some m, some nm => do aff_proof g name pe; line; do aff_proof g name pz; line; IO.println (s!"{name s} because pre-composed by the epi {m.name} the map is  {nm.name} which is zero")
        |_,_ => IO.println "The proof is wrong 28"

      |Proof.MapIsZero_ExactMonoWithMap pex pm s => match StatementOfProof pex with
        |Statement.IsExact _ n => let n:=g.edges[n]?
            match n with
              |none => IO.println "The proof is wrong 29"
              |some n => do aff_proof g name pex; line; aff_proof g name pm; line; IO.println (s!"{name s} because {n.name} is a mono and the composition is exact")
        |_ => IO.println "The proof is wrong 30"

      |Proof.MapIsZero_ExactMapWithEpi p1 p2 s => match StatementOfProof p1 with
        |Statement.IsExact m _ => let m:=g.edges[m]?
            match m with
              |none => IO.println "The proof is wrong 31"
              |some m => do aff_proof g name p1; line; aff_proof g name p2;line; IO.println (s!"{name s} because {m.name} is an epi and the composition is exact")
        |_ => IO.println "The proof is wrong 32"

      |Proof.MapIsZero_ExtramuralOfZero p s => match StatementOfProof p with
        |Statement.IsZeroMap m => let m:=g.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 33"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name_shad s} because it's the extramural map of {m.name} which is zero")
        |_ => IO.println "The proof is wrong 34"

      |Proof.MapIsMono_IsKer m s => let m:=g.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 35"
            |some m => IO.println (s!"{name s} because it's the kernel of {m.name}")

      |Proof.MapIsMono_IsIso p s => do aff_proof g name p; line; IO.println (s!"{name s} because it's an isomorphism")

      |Proof.MapIsMono_CompOfMono p1 p2 s => match StatementOfProof p1,StatementOfProof p2 with
        |Statement.IsMonoMap m,Statement.IsMonoMap n => let m:=g.edges[m]?
            let n:=g.edges[n]?
            match m,n with
              |none,_ => IO.println "The proof is wrong 36"
              |_,none => IO.println "The proof is wrong 37"
              |some m, some n => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the composition of {m.name} with {n.name} and they are mono")
        |_,_ => IO.println "The proof is wrong 38"

      |Proof.MapIsMono_PostCompIsMono m p s => match StatementOfProof p with
        |Statement.IsMonoMap nm => let m:=g.edges[m]?
            let nm:=g.edges[nm]?
            match m,nm with
              |none,_ => IO.println "The proof is wrong 39"
              |_,none => IO.println "The proof is wrong 40"
              |some m, some nm => do aff_proof g name p; IO.println (s!"{name s} because post-composed by  {m.name} the map is  {nm.name} which is a mono")
        | _ => IO.println "The proof is wrong 41"

      |Proof.MapIsMono_ExactMapWithZero p1 p2 s => match StatementOfProof p1, StatementOfProof p2 with
        |Statement.IsExact _ _ ,Statement.IsZeroMap n => let n:=g.edges[n]?
          match n with
            |none => IO.println "The proof is wrong 42"
            |some n => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because the composition with the zero map {n.name} is exact")
        |_,_ => IO.println "The proof is wrong 43"

      |Proof.MapIsMono_DomainIsZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:= g.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 44"
            |some a => do aff_proof g name p; line; IO.println (s!"{name s} because the domain {a.name} is zero")
        |_ => IO.println "The proof is wrong 45"

      |Proof.MapIsEpi_IsCoKer n s => let n:=g.edges[n]?
        match n with
          |none => IO.println "The proof is wrong 46"
          |some n => IO.println (s!"{name s} because it's the cokernel of the map {n.name}")

      |Proof.MapIsEpi_IsIso p s => match StatementOfProof p with
        |Statement.IsIsoMap _ => do aff_proof g name p; IO.println (s!"{name s} because it's an isomorphism")
        |_ => IO.println "The proof is wrong 47"

      |Proof.MapIsEpi_CompOfEpi p1 p2 s => match StatementOfProof p1, StatementOfProof p2 with
        |Statement.IsEpiMap m,Statement.IsEpiMap n => let m:=g.edges[m]?
            let n:=g.edges[n]?
            match m,n with
              |none,_ => IO.println "The proof is wrong 48"
              |_,none => IO.println "The proof is wrong 49"
              |some m, some n => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the composition of the epi {n.name} with the epi {m.name}")
        |_,_ => IO.println "The proof is wrong 50"

      |Proof.MapIsEpi_PreCompIsEpi m p s => match StatementOfProof p with
        |Statement.IsEpiMap nm => let m:=g.edges[m]?
            let nm:=g.edges[nm]?
            match m,nm with
              |none,_ => IO.println "The proof is wrong 51"
              |_,none => IO.println "The proof is wrong 52"
              |some m, some nm => do aff_proof g name p; line; IO.println (s!"{name s} because precomposed by {m.name} it's the epi {nm.name}")
        |_ => IO.println "The proof is wrong 53"

      |Proof.MapIsEpi_ExactZeroWithMap p1 p2 s =>  match StatementOfProof p1 with
        |Statement.IsExact m n => let m:=g.edges[m]?
            let n:=g.edges[n]?
            match m,n with
              |none,_ => IO.println "The proof is wrong 54"
              |_,none => IO.println "The proof is wrong 55"
              |some m, some n => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because the composition of {n.name} with {m.name} is exact and {n.name} is a zero map")
        |_ => IO.println "The proof is wrong 56"

      |Proof.MapIsEpi_CoDomainIsZero p s => match StatementOfProof p with
        |Statement.IsZeroObj b => let b:=g.vertex[b]?
          match b with
            |none => IO.println "The proof is wrong 57"
            |some b => do aff_proof g name p; line; IO.println (s!"{name s} because it's codomain {b.name} is a zero object")
        |_ => IO.println "The proof is wrong 58"

      |Proof.MapIsIso_MonoAndEpiMap p1 p2 s => do aff_proof g name p1 ; line; aff_proof g name p2 ; line; IO.println (s!"{name s} because it's a mono and an epi")

      |Proof.ObjectIsZero_DomainOfMonoZero p1 p2 s => match StatementOfProof p1 with
        |Statement.IsMonoMap m => let m:=g.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 59"
            |some m => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the domain of the mono-zero map {m.name}")
        |_ => IO.println "The proof is wrong 60"

      |Proof.ObjectIsZero_CoDomainOfEpiZero p1 p2 s => match StatementOfProof p1 with
        |Statement.IsEpiMap m => let m:=g.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 61"
            |some m => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the codomain of the epi-zero map {m.name}")
        |_ => IO.println "The proof is wrong 62"

      |Proof.ObjectIsZero_DonnorOfZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:= gr.struct.vertex[a]?
          match a with
            |none =>  IO.println "The proof is wrong 63"
            |some a => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the donor of the zero object {a.name}}")
        |_ => IO.println "The proof is wrong 64"

      |Proof.ObjectIsZero_DonorOfDomainOfDiagMono p s => match StatementOfProof p with
        |Statement.IsMonoMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 65"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the donor of the domain of the diagonal mono-map {m.name}")
        |_ => IO.println "The proof is wrong 66"

      |Proof.ObjectIsZero_DonorOfDomainOfHorizEpi p s => match StatementOfProof p with
        |Statement.IsEpiMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 67"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the donor of the domain of the horizontal epi-map {m.name}")
        |_ => IO.println "The proof is wrong 68"

      |Proof.ObjectIsZero_DonorOfCoDomainOfVerticEpi p s => match StatementOfProof p with
        |Statement.IsEpiMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 69"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the donor of the codomain of the vertical epi-map {m.name}")
        |_ => IO.println "The proof is wrong 70"

      |Proof.ObjectIsZero_ReceptorOfZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:= gr.struct.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 71"
            |some a => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the receptor of the zero object {a.name}")
        |_ => IO.println "The proof is wrong 72"

      |Proof.ObjectIsZero_ReceptorOfCoDomainOfDiagEpi p s => match StatementOfProof p with
        |Statement.IsEpiMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 73"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the receptor of the codomain of the vertical epi-map {m.name}")
        |_ => IO.println "The proof is wrong 74"

      |Proof.ObjectIsZero_ReceptorOfDomainOfHorizMono p s => match StatementOfProof p with
        |Statement.IsMonoMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 75"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the receptor of the domain of the horizontal mono-map {m.name}")
        |_ => IO.println "The proof is wrong 76"

      |Proof.ObjectIsZero_ReceptorOfDomainOfVerticMono p s => match StatementOfProof p with
        |Statement.IsMonoMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 77"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the receptor of the domain of the vertical mono-map {m.name}")
        |_ => IO.println "The proof is wrong 78"

      |Proof.ObjectIsZero_hHomOfZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:= gr.struct.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 79"
            |some a => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the hHom of the zero object {a.name}")
        |_ => IO.println "The proof is wrong 80"

      |Proof.ObjectIsZero_hHomOfExact p s => match StatementOfProof p with
        |Statement.IsExact m n => let m:=gr.struct.edges[m]?
          let n:= gr.struct.edges[n]?
          match m,n with
            |none,_ => IO.println "The proof is wrong 81"
            |_,none => IO.println "The proof is wrong 82"
            |some m, some n => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the hHom of the exact composition of {n.name} with {m.name}")
        |_ => IO.println "The proof is wrong 83"

      |Proof.ObjectIsZero_hHomOfDomainOfHorizEpi p s => match StatementOfProof p with
        |Statement.IsEpiMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 84"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the hHom of the domain of the horizontal epi-map {m.name}")
        |_ => IO.println "The proof is wrong 85"

      |Proof.ObjectIsZero_hHomOfDomainOfHorizMono p s => match StatementOfProof p with
        |Statement.IsMonoMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 86"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the hHom of the domain of the horizontal mono-map {m.name}")
        |_ => IO.println "The proof is wrong 87"

      |Proof.ObjectIsZero_vHomOfZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:= gr.struct.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 88"
            |some a => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the vHom of the zero object {a.name}")
        |_ => IO.println "The proof is wrong 89"

      |Proof.ObjectIsZero_vHomOfExact p s => match StatementOfProof p with
        |Statement.IsExact m n => let m:=gr.struct.edges[m]?
          let n:= gr.struct.edges[n]?
          match m,n with
            |none,_ => IO.println "The proof is wrong 90"
            |_,none => IO.println "The proof is wrong 91"
            |some m, some n => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the vHom of the exact composition of {n.name} with {m.name}")
        |_ => IO.println "The proof is wrong 92"

      |Proof.ObjectIsZero_vHomOfVerticMono p s => match StatementOfProof p with
        |Statement.IsMonoMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 93"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the vHom of the vertical mono-map {m.name}")
        |_ => IO.println "The proof is wrong 94"

      |Proof.ObjectIsZero_vHomOfVerticEpi p s => match StatementOfProof p with
        |Statement.IsEpiMap m => let m:= gr.struct.edges[m]?
          match m with
            |none => IO.println "The proof is wrong 95"
            |some m => do aff_proof gr.struct name_st p; line; IO.println (s!"{name s} because it's the vHom of the vertical epi-map {m.name}")
        |_ => IO.println "The proof is wrong 96"

      |Proof.ObjectsAreIso_IsoItself s => IO.println (s!"{name s} by the identity morphism")

      |Proof.ObjectsAreIso_IsoTrans p1 p2 s => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} by transitivity")

      |Proof.CompIsExact_KerAndMap s => IO.println (s!"{name s} because it's the composition of a map with it's kernel")

      |Proof.CompIsExact_MapAndCoKer s => IO.println (s!"{name s} because it's the composition of a cokernel with it's map")

      |Proof.CompIsExact_ZeroWithMono p1 p2 s => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the composition of a mono-map with a zero map")

      |Proof.CompIsExact_EpiWithZero p1 p2 s => do aff_proof g name p1; line; aff_proof g name p2; line; IO.println (s!"{name s} because it's the composition of a zero-map with a epi map")

      |Proof.CompIsExact_hHomIsZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:=gr.shadow.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 97"
            |some a => do aff_proof gr.shadow name_shad p; line; IO.println (s!"{name s} because it's hHom {a.name} is a zero object")
        |_ => IO.println "The proof is wrong 98"

      |Proof.CompIsExact_vHomIsZero p s => match StatementOfProof p with
        |Statement.IsZeroObj a => let a:=gr.shadow.vertex[a]?
          match a with
            |none => IO.println "The proof is wrong 99"
            |some a => do aff_proof gr.shadow name_shad p; line; IO.println (s!"{name s} because it's vHom {a.name} is a zero object")
        |_ => IO.println "The proof is wrong 100"

      |Proof.CompIsExact_HorizontalSalamnder c a b d s => let a:=gr.struct.vertex[a]?
        let b:=gr.struct.vertex[b]?
        let c:=gr.struct.vertex[c]?
        let d:=gr.struct.vertex[d]?
        match a,b,c,d with
          |none,_,_,_ => IO.println "The proof is wrong 101"
          |_,none,_,_ => IO.println "The proof is wrong 102"
          |_,_,none,_ => IO.println "The proof is wrong 103"
          |_,_,_,none => IO.println "The proof is wrong 104"
          |some a, some b, some c, some d => IO.println (s!"{name s} because it's part of the exact sequence induced by {c.name}->{a.name}->{b.name}->{d.name} and the horizontal salamander lemma")

      |Proof.CompIsExact_VerticalSalamander c a b d s => let a:=gr.struct.vertex[a]?
        let b:=gr.struct.vertex[b]?
        let c:=gr.struct.vertex[c]?
        let d:=gr.struct.vertex[d]?
        match a,b,c,d with
          |none,_,_,_ => IO.println "The proof is wrong 105"
          |_,none,_,_ => IO.println "The proof is wrong 106"
          |_,_,none,_ => IO.println "The proof is wrong 107"
          |_,_,_,none => IO.println "The proof is wrong 108"
          |some a, some b, some c, some d => IO.println (s!"{name s} because it's part of the exact sequence induced by {c.name}->{a.name}->{b.name}->{d.name} and the vertical salamander lemma")

    aff_proof gr.struct name_st p

/-In this file I build the terms to express the statements and the proofs i want to have on a diagram defined by a grid (from the file Grid)-/

inductive Statement where
  |Nothing: Statement
  |IsZeroMap: Nat→Statement
  |IsZeroObj: Nat→Statement
  |IsMonoMap: Nat→Statement
  |IsEpiMap: Nat→Statement
  |IsIsoMap: Nat→Statement
  |IsExact: Nat→Nat→Statement
  |AreIsoObj: Nat→Nat→Statement
deriving Repr

/-Somme arguments have extra argument of type Nat, the goal is to find all the objects involved in the argument if their name is not in the context-/

inductive Proof where
  |Assumption: Statement→Proof
  |MapIsZero_DomainIsZero: Proof→Statement→Proof
  |MapIsZero_CoDomainIsZero: Proof→Statement→Proof
  |MapIsZero_PreCompByZero: Proof→Nat→Statement→Proof
  |MapIsZero_PostCompByZero: Nat→Proof→Statement→Proof
  |MapIsZero_ExactComp: Proof→Statement→Proof
  |MapIsZero_HCompInDCC: Nat→Nat→Statement→Proof
  |MapIsZero_VCompInDCC: Nat→Nat→Statement→Proof
  |MapIsZero_PosCompByMonoIsZero: Proof→Proof→Statement→Proof
  |MapIsZero_PreCompByEpiIsZero: Proof→Proof→Statement→Proof
  |MapIsZero_ExactMonoWithMap: Proof→Proof→Statement→Proof
  |MapIsZero_ExactMapWithEpi: Proof→Proof→Statement→Proof
  |MapIsZero_ExtramuralOfZero: Proof→Statement→Proof
  |MapIsMono_IsKer: Nat→Statement→Proof
  |MapIsMono_IsIso: Proof→Statement→Proof
  |MapIsMono_CompOfMono: Proof→Proof→Statement→Proof
  |MapIsMono_PostCompIsMono: Nat→Proof→Statement→Proof
  |MapIsMono_ExactMapWithZero: Proof→Proof→Statement→Proof
  |MapIsMono_DomainIsZero: Proof→Statement→Proof
  |MapIsEpi_IsCoKer: Nat→Statement→Proof
  |MapIsEpi_IsIso: Proof→Statement→ Proof
  |MapIsEpi_CompOfEpi: Proof→Proof→Statement→Proof
  |MapIsEpi_PreCompIsEpi: Nat→Proof→Statement→Proof
  |MapIsEpi_ExactZeroWithMap: Proof→Proof→Statement→Proof
  |MapIsEpi_CoDomainIsZero: Proof→Statement→Proof
  |MapIsIso_MonoAndEpiMap: Proof→Proof→Statement→Proof
  |ObjectIsZero_DomainOfMonoZero: Proof→Proof→Statement→Proof
  |ObjectIsZero_CoDomainOfEpiZero: Proof→Proof→Statement→Proof
  |ObjectIsZero_DonnorOfZero: Proof→Statement→Proof
  |ObjectIsZero_DonorOfDomainOfDiagMono: Proof→Statement→Proof
  |ObjectIsZero_DonorOfDomainOfHorizEpi: Proof→Statement→Proof
  |ObjectIsZero_DonorOfCoDomainOfVerticEpi: Proof→Statement→Proof
  |ObjectIsZero_ReceptorOfZero: Proof→Statement→Proof
  |ObjectIsZero_ReceptorOfCoDomainOfDiagEpi: Proof→Statement→Proof
  |ObjectIsZero_ReceptorOfDomainOfHorizMono: Proof→Statement→Proof
  |ObjectIsZero_ReceptorOfDomainOfVerticMono: Proof→Statement→Proof
  |ObjectIsZero_hHomOfZero: Proof→Statement→Proof
  |ObjectIsZero_hHomOfExact: Proof→Statement→Proof
  |ObjectIsZero_hHomOfDomainOfHorizEpi: Proof→Statement→Proof
  |ObjectIsZero_hHomOfDomainOfHorizMono: Proof→Statement→Proof
  |ObjectIsZero_vHomOfZero: Proof→Statement→Proof
  |ObjectIsZero_vHomOfExact: Proof→Statement→Proof
  |ObjectIsZero_vHomOfVerticMono: Proof→Statement→Proof
  |ObjectIsZero_vHomOfVerticEpi: Proof→Statement→Proof
  |ObjectsAreIso_IsoItself: Statement→Proof
  |ObjectsAreIso_IsoTrans: Proof→Proof→Statement→Proof
  |CompIsExact_KerAndMap: Statement→Proof
  |CompIsExact_MapAndCoKer: Statement→Proof
  |CompIsExact_ZeroWithMono: Proof→Proof→Statement→Proof
  |CompIsExact_EpiWithZero: Proof→Proof→Statement→Proof
  |CompIsExact_hHomIsZero: Proof→Statement→Proof
  |CompIsExact_vHomIsZero: Proof→Statement→Proof
  |CompIsExact_HorizontalSalamnder: Nat→Nat→Nat→Nat→Statement→Proof
  |CompIsExact_VerticalSalamander: Nat→Nat→Nat→Nat→Statement→Proof
deriving Repr

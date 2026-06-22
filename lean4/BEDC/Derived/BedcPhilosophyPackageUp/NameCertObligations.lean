import BEDC.Derived.BedcPhilosophyPackageUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BedcPhilosophyPackageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BedcPhilosophyPackageCarrier [AskSetup] [PackageSetup]
    (T R M G D S C A H K N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory D ∧
    UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory K ∧
      UnaryHistory N ∧ Cont T R K ∧ Cont M G K ∧ Cont S A K ∧ Cont C A K ∧
        PkgSig bundle K pkg ∧ PkgSig bundle N pkg

theorem BedcPhilosophyPackage_namecert_obligations [AskSetup] [PackageSetup]
    {T R M G D S C A H K N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  have sourceN :
      (fun row : BHist =>
        BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N) N := by
    exact ⟨carrier, hsame_refl N⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem BedcPhilosophyPackage_audit_map_nonescape [AskSetup] [PackageSetup]
    {T R M G D S C A H K N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      UnaryHistory S ∧ UnaryHistory A ∧ Cont S A K ∧
        PkgSig bundle K pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  exact
    ⟨carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem BedcPhilosophyPackage_registry_ledger_exactness [AskSetup] [PackageSetup]
    {T R M G D S C A H K N entryRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      (hsame entryRead T ∨ hsame entryRead R ∨ hsame entryRead M ∨ hsame entryRead G ∨
        hsame entryRead D ∨ hsame entryRead S ∨ hsame entryRead C ∨ hsame entryRead A ∨
          hsame entryRead H ∨ hsame entryRead K ∨ hsame entryRead N) →
        SemanticNameCert
            (fun row : BHist => (hsame row entryRead ∨ hsame row N) ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row T ∨ hsame row R ∨ hsame row M ∨ hsame row G ∨
                hsame row D ∨ hsame row S ∨ hsame row C ∨ hsame row A ∨
                  hsame row H ∨ hsame row K ∨ hsame row N ∨ hsame row entryRead)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg)
            hsame ∧
          UnaryHistory entryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier entryMember
  have unaryT : UnaryHistory T := carrier.left
  have unaryR : UnaryHistory R := carrier.right.left
  have unaryM : UnaryHistory M := carrier.right.right.left
  have unaryG : UnaryHistory G := carrier.right.right.right.left
  have unaryD : UnaryHistory D := carrier.right.right.right.right.left
  have unaryS : UnaryHistory S := carrier.right.right.right.right.right.left
  have unaryC : UnaryHistory C := carrier.right.right.right.right.right.right.left
  have unaryA : UnaryHistory A := carrier.right.right.right.right.right.right.right.left
  have unaryH : UnaryHistory H := carrier.right.right.right.right.right.right.right.right.left
  have unaryK : UnaryHistory K := carrier.right.right.right.right.right.right.right.right.right.left
  have unaryN : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have pkgK : PkgSig bundle K pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgN : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have entryUnary : UnaryHistory entryRead := by
    cases entryMember with
    | inl sameT =>
        exact unary_transport_symm unaryT sameT
    | inr rest =>
        cases rest with
        | inl sameR =>
            exact unary_transport_symm unaryR sameR
        | inr rest =>
            cases rest with
            | inl sameM =>
                exact unary_transport_symm unaryM sameM
            | inr rest =>
                cases rest with
                | inl sameG =>
                    exact unary_transport_symm unaryG sameG
                | inr rest =>
                    cases rest with
                    | inl sameD =>
                        exact unary_transport_symm unaryD sameD
                    | inr rest =>
                        cases rest with
                        | inl sameS =>
                            exact unary_transport_symm unaryS sameS
                        | inr rest =>
                            cases rest with
                            | inl sameC =>
                                exact unary_transport_symm unaryC sameC
                            | inr rest =>
                                cases rest with
                                | inl sameA =>
                                    exact unary_transport_symm unaryA sameA
                                | inr rest =>
                                    cases rest with
                                    | inl sameH =>
                                        exact unary_transport_symm unaryH sameH
                                    | inr rest =>
                                        cases rest with
                                        | inl sameK =>
                                            exact unary_transport_symm unaryK sameK
                                        | inr sameN =>
                                            exact unary_transport_symm unaryN sameN
  have sourceEntry :
      (fun row : BHist => (hsame row entryRead ∨ hsame row N) ∧ UnaryHistory row)
        entryRead := by
    exact ⟨Or.inl (hsame_refl entryRead), entryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row entryRead ∨ hsame row N) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row R ∨ hsame row M ∨ hsame row G ∨
              hsame row D ∨ hsame row S ∨ hsame row C ∨ hsame row A ∨
                hsame row H ∨ hsame row K ∨ hsame row N ∨ hsame row entryRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro entryRead sourceEntry
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        constructor
        · cases source.left with
          | inl sameEntry =>
              exact Or.inl (hsame_trans (hsame_symm same) sameEntry)
          | inr sameN =>
              exact Or.inr (hsame_trans (hsame_symm same) sameN)
        · exact unary_transport source.right same
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEntry =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr sameEntry))))))))))
      | inr sameN =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl sameN))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgK, pkgN⟩
  }
  exact ⟨cert, entryUnary⟩

end BEDC.Derived.BedcPhilosophyPackageUp

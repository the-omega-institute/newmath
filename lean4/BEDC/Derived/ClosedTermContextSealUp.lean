import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ClosedTermContextSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedTermContextSealCarrier [AskSetup] [PackageSetup]
    (E Q T B S O H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory E ∧ UnaryHistory Q ∧ UnaryHistory T ∧ UnaryHistory B ∧
    UnaryHistory S ∧ UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont E Q T ∧ Cont T B S ∧
        Cont S O C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ClosedTermContextSeal_namecert_obligations [AskSetup] [PackageSetup]
    {E Q T B S O H C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermContextSealCarrier E Q T B S O H C P N bundle pkg →
      Cont O C auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row E ∨ hsame row Q ∨ hsame row T ∨ hsame row B ∨
                  hsame row S ∨ hsame row O ∨ hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory E ∧ UnaryHistory Q ∧ UnaryHistory T ∧ UnaryHistory B ∧
              UnaryHistory S ∧ UnaryHistory O ∧ UnaryHistory C ∧
                UnaryHistory auditRead ∧ Cont E Q T ∧ Cont T B S ∧
                  Cont S O C ∧ Cont O C auditRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditRoute auditPkg
  obtain ⟨EUnary, QUnary, TUnary, BUnary, SUnary, OUnary, _HUnary, CUnary,
    _PUnary, _NUnary, emptyClosedRoute, typedNormalRoute, obstructionRoute,
    provenancePkg, localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed OUnary CUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row Q ∨ hsame row T ∨ hsame row B ∨
              hsame row S ∨ hsame row O ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead
        ⟨hsame_refl auditRead, auditUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, auditPkg⟩
  }
  exact
    ⟨cert, EUnary, QUnary, TUnary, BUnary, SUnary, OUnary, CUnary, auditUnary,
      emptyClosedRoute, typedNormalRoute, obstructionRoute, auditRoute, provenancePkg,
      localNamePkg, auditPkg⟩

theorem ClosedTermContextSeal_subject_reduction_handoff [AskSetup] [PackageSetup]
    {E Q T B S O H C P N handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermContextSealCarrier E Q T B S O H C P N bundle pkg →
      Cont S C handoffRead →
        PkgSig bundle handoffRead pkg →
          UnaryHistory E ∧ UnaryHistory Q ∧ UnaryHistory T ∧ UnaryHistory B ∧
            UnaryHistory S ∧ UnaryHistory O ∧ UnaryHistory handoffRead ∧
              Cont E Q T ∧ Cont T B S ∧ Cont S C handoffRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier handoffRoute handoffPkg
  obtain ⟨EUnary, QUnary, TUnary, BUnary, SUnary, OUnary, _HUnary, CUnary,
    _PUnary, _NUnary, emptyClosedRoute, typedNormalRoute, _obstructionRoute,
    provenancePkg, localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed SUnary CUnary handoffRoute
  exact
    ⟨EUnary, QUnary, TUnary, BUnary, SUnary, OUnary, handoffUnary,
      emptyClosedRoute, typedNormalRoute, handoffRoute, provenancePkg, localNamePkg,
      handoffPkg⟩

end BEDC.Derived.ClosedTermContextSealUp

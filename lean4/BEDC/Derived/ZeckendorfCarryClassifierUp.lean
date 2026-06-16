import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZeckendorfCarryClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZeckendorfCarryClassifierCarrier [AskSetup] [PackageSetup]
    (u v c s t h r p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory c ∧ UnaryHistory s ∧
    UnaryHistory t ∧ UnaryHistory p ∧ Cont u v c ∧ Cont c s r ∧ Cont r t h ∧
      Cont h p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg

theorem ZeckendorfCarryClassifierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {u v c s t h r p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryClassifierCarrier u v c s t h r p n bundle pkg ->
      UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory c ∧ UnaryHistory s ∧
        UnaryHistory t ∧ UnaryHistory h ∧ UnaryHistory r ∧ UnaryHistory p ∧
          UnaryHistory n ∧ Cont u v c ∧ Cont c s r ∧ PkgSig bundle n pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨uUnary, vUnary, cUnary, sUnary, tUnary, pUnary, uvCarry, carrySumRead,
    readTailHandoff, handoffProvenanceName, _provenancePkg, namePkg⟩ := carrier
  have rUnary : UnaryHistory r :=
    unary_cont_closed cUnary sUnary carrySumRead
  have hUnary : UnaryHistory h :=
    unary_cont_closed rUnary tUnary readTailHandoff
  have nUnary : UnaryHistory n :=
    unary_cont_closed hUnary pUnary handoffProvenanceName
  exact
    ⟨uUnary, vUnary, cUnary, sUnary, tUnary, hUnary, rUnary, pUnary, nUnary,
      uvCarry, carrySumRead, namePkg⟩

theorem ZeckendorfCarryClassifierCarrier_nonescape_boundary [AskSetup] [PackageSetup]
    {u v c s t h r p n publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryClassifierCarrier u v c s t h r p n bundle pkg ->
      Cont c r publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row u ∨ hsame row v ∨ hsame row c ∨ hsame row h ∨
                  hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ Cont c r publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory c ∧ UnaryHistory r ∧
              UnaryHistory h ∧ UnaryHistory publicRead ∧ Cont u v c ∧ Cont c s r ∧
                Cont r t h ∧ Cont c r publicRead ∧ PkgSig bundle n pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier carryReadPublic publicReadPkg
  obtain ⟨uUnary, vUnary, cUnary, sUnary, tUnary, _pUnary, uvCarry, carrySumRead,
    readTailHandoff, _handoffProvenanceName, _provenancePkg, namePkg⟩ := carrier
  have rUnary : UnaryHistory r :=
    unary_cont_closed cUnary sUnary carrySumRead
  have hUnary : UnaryHistory h :=
    unary_cont_closed rUnary tUnary readTailHandoff
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed cUnary rUnary carryReadPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row u ∨ hsame row v ∨ hsame row c ∨ hsame row h ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont c r publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        (And.intro (hsame_refl publicRead) publicReadUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro carryReadPublic publicReadPkg)
  }
  exact
    ⟨cert, uUnary, vUnary, cUnary, rUnary, hUnary, publicReadUnary, uvCarry, carrySumRead,
      readTailHandoff, carryReadPublic, namePkg, publicReadPkg⟩

theorem ZeckendorfCarryClassifier_window_determinacy [AskSetup] [PackageSetup]
    {u v c s t h r p n carriedRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ZeckendorfCarryClassifierCarrier u v c s t h r p n bundle pkg ->
      Cont c r carriedRead ->
        PkgSig bundle carriedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row carriedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row u ∨ hsame row v ∨ hsame row c ∨ hsame row r ∨
                  hsame row carriedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont u v c ∧ Cont c s r ∧ Cont c r carriedRead ∧
                  PkgSig bundle carriedRead pkg)
              hsame ∧
            UnaryHistory carriedRead ∧ Cont u v c ∧ Cont c s r ∧
              Cont c r carriedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier carryReadRoute carriedReadPkg
  obtain ⟨uUnary, vUnary, cUnary, sUnary, _tUnary, _pUnary, uvCarry, carrySumRead,
    _readTailHandoff, _handoffProvenanceName, _provenancePkg, _namePkg⟩ := carrier
  have rUnary : UnaryHistory r :=
    unary_cont_closed cUnary sUnary carrySumRead
  have carriedReadUnary : UnaryHistory carriedRead :=
    unary_cont_closed cUnary rUnary carryReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row carriedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row u ∨ hsame row v ∨ hsame row c ∨ hsame row r ∨
              hsame row carriedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont u v c ∧ Cont c s r ∧ Cont c r carriedRead ∧
              PkgSig bundle carriedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro carriedRead
        (And.intro (hsame_refl carriedRead) carriedReadUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, uvCarry, carrySumRead, carryReadRoute, carriedReadPkg⟩
  }
  exact ⟨cert, carriedReadUnary, uvCarry, carrySumRead, carryReadRoute⟩

end BEDC.Derived.ZeckendorfCarryClassifierUp

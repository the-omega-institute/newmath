import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceNamecertObligations [AskSetup] [PackageSetup]
    {source modulus selector fast regular readback real transport replay provenance localName
      modulusRead selectorRead fastRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory modulus ->
        UnaryHistory selector ->
          UnaryHistory fast ->
            UnaryHistory regular ->
              UnaryHistory readback ->
                UnaryHistory real ->
                  Cont source modulus modulusRead ->
                    Cont modulusRead selector selectorRead ->
                      Cont selectorRead fast fastRead ->
                        Cont fastRead regular regularRead ->
                          Cont regularRead real realRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row realRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row source ∨ hsame row modulus ∨
                                        hsame row selector ∨ hsame row fast ∨
                                          hsame row regular ∨ hsame row readback ∨
                                            hsame row real ∨ hsame row realRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory modulusRead ∧
                                    UnaryHistory selectorRead ∧
                                      UnaryHistory fastRead ∧
                                        UnaryHistory regularRead ∧
                                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro sourceUnary modulusUnary selectorUnary fastUnary regularUnary _readbackUnary
    realUnary modulusRoute selectorRoute fastRoute regularRoute realRoute provenancePkg
    localNamePkg
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary modulusUnary modulusRoute
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusReadUnary selectorUnary selectorRoute
  have fastReadUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorReadUnary fastUnary fastRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed fastReadUnary regularUnary regularRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularReadUnary realUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row modulus ∨ hsame row selector ∨
              hsame row fast ∨ hsame row regular ∨ hsame row readback ∨
                hsame row real ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        intro _row _other sameRows sourceSpec
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceSpec.left,
            unary_transport sourceSpec.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceSpec
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceSpec.left))))))
    ledger_sound := by
      intro _row sourceSpec
      exact ⟨sourceSpec.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, modulusReadUnary, selectorReadUnary, fastReadUnary, regularReadUnary,
      realReadUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp

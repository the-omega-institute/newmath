import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealNameClassifierSourcePacketRows [AskSetup] [PackageSetup]
    (A B W DA DB T RA RB H K P S N : BHist) : List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  [A, B, W, DA, DB, T, RA, RB, H, K, P, S, N]

theorem RealNameClassifierSourcePacketRows_complete [AskSetup] [PackageSetup]
    {A B W DA DB T RA RB H K P S N classifierRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierSourcePacketRows A B W DA DB T RA RB H K P S N =
        [A, B, W, DA, DB, T, RA, RB, H, K, P, S, N] ->
      UnaryHistory W -> UnaryHistory DA -> UnaryHistory DB ->
        Cont W DA classifierRead -> Cont classifierRead DB sealRead ->
          PkgSig bundle P pkg -> PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                  hsame row DB ∨ hsame row T ∨ hsame row RA ∨ hsame row RB ∨
                    hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row S ∨
                      hsame row N ∨ Cont W DA classifierRead ∨
                        Cont classifierRead DB sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rows windowUnary leftTolUnary rightTolUnary classifierRoute sealRoute provenancePkg
    localNamePkg
  have _acceptedRows :
      RealNameClassifierSourcePacketRows A B W DA DB T RA RB H K P S N =
        [A, B, W, DA, DB, T, RA, RB, H, K, P, S, N] := rows
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary leftTolUnary classifierRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary rightTolUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
            hsame row T ∨ hsame row RA ∨ hsame row RB ∨ hsame row H ∨ hsame row K ∨
              hsame row P ∨ hsame row S ∨ hsame row N ∨ Cont W DA classifierRead ∨
                Cont classifierRead DB sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr sealRoute)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, classifierUnary, sealUnary⟩

end BEDC.Derived.RealNameClassifierUp

from fractions import Fraction

from source_norm_cert import SourceNormCertificate, SourceNormTerm, ldl_source_norm_certificate


def check_ldl_demo_reconstructs_and_reads_quadratic():
    matrix = [
        [Fraction(2), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(2), Fraction(0)],
        [Fraction(1), Fraction(0), Fraction(2)],
    ]
    cert = ldl_source_norm_certificate(matrix)
    cert.verify()
    assert cert.reconstructed_matrix() == tuple(tuple(row) for row in matrix)
    coeffs = [Fraction(3), Fraction(-2), Fraction(5)]
    assert cert.verify_quadratic_readback(coeffs) == cert.quadratic_value(coeffs)
    assert cert.square_value(coeffs) >= 0


def check_explicit_square_terms_reconstruct_rank_one_packet():
    matrix = (
        (Fraction(4), Fraction(6)),
        (Fraction(6), Fraction(9)),
    )
    cert = SourceNormCertificate(
        matrix=matrix,
        terms=(SourceNormTerm(Fraction(1), (Fraction(2), Fraction(3)), "rank-one"),),
    )
    cert.verify()
    assert cert.reconstructed_matrix() == matrix
    assert cert.verify_quadratic_readback([Fraction(5), Fraction(-1)]) == Fraction(49)


def check_indefinite_matrix_is_rejected():
    try:
        ldl_source_norm_certificate([[Fraction(1), Fraction(2)], [Fraction(2), Fraction(1)]])
    except ValueError:
        return
    raise AssertionError("indefinite matrix was accepted")


if __name__ == "__main__":
    check_ldl_demo_reconstructs_and_reads_quadratic()
    check_explicit_square_terms_reconstruct_rank_one_packet()
    check_indefinite_matrix_is_rejected()
    print("ok")

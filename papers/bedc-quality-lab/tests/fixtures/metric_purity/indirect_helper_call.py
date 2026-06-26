def private_bonus(row):
    return 0.1 if row["score"] > 0.0 else 0.0


def metric_projection(rows):
    return {"quality_q": sum(row["score"] + private_bonus(row) for row in rows) / len(rows)}

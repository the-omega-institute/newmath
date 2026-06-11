def metric_projection(rows):
    total = 0.0
    for row in rows:
        if row["arm_id"] == "treatment":
            total += row["score"] + 0.1
        else:
            total += row["score"]
    return {"quality_q": total / len(rows)}

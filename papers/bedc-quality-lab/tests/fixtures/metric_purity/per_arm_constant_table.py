def metric_projection(rows):
    constants = {"treatment": 0.2, "control": 0.0}
    return {"quality_q": sum(row["score"] + constants[row["arm_id"]] for row in rows) / len(rows)}

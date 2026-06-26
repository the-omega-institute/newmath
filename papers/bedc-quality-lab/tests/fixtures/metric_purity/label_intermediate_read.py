def metric_projection(rows):
    hits = [1.0 if row["label"] == 1 else 0.0 for row in rows]
    return {"quality_q": sum(hits) / len(hits)}

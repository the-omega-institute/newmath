def metric_projection(rows):
    score = sum(row["score"] for row in rows) / len(rows)
    feature_mode = rows[0]["feature_mode"]
    if feature_mode == "privileged":
        score += 0.2
    return {"quality_q": score}

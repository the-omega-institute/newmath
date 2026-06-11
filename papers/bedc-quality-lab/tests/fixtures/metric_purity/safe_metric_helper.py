def registered_average(rows):
    return sum(row["score"] for row in rows) / len(rows)


def metric_projection(rows):
    return {"quality_q": registered_average(rows)}

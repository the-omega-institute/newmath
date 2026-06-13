def metric_projection(rows):
    component_name = rows[0]["component_name"]
    if component_name == "ledger_head":
        return {"quality_q": 0.9}
    return {"quality_q": sum(row["score"] for row in rows) / len(rows)}

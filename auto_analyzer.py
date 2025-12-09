#!/usr/bin/env python3
# -- coding: utf-8 --
import numpy as np
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity
from xgboost import XGBClassifier

# Simulate historical data (defect type: PB001 = product defect, PB002 = environmental problem)
history_logs = [
    {"text": "AssertionError: expected 200 got 404", "defect": "PB001"},
    {"text": "Connection timeout to database", "defect": "PB002"}
]
# New logs to be analyzed
new_log = "Assertion failed: status 404 not found"

# 1. TF-IDF Text Tokenization and Vectorization
vectorizer = TfidfVectorizer()
corpus = [log["text"] for log in history_logs] + [new_log]
tfidf_matrix = vectorizer.fit_transform(corpus)

# 2. Calculate similarity (cosine similarity)
new_vec = tfidf_matrix[-1]
history_vecs = tfidf_matrix[:-1]
similarities = cosine_similarity(new_vec, history_vecs).flatten()

# 3. Add a boost factor (example: manually analyzed log weight x10)
boosts = np.array([10.0 if log["defect"] == "PB001" else 1.0 for log in history_logs])  # 模拟PB001优先级
boosted_scores = similarities * boosts

# 4. Simulating XGBoost decisions (simplified feature engineering)
top_index = np.argmax(boosted_scores)
top_defect = history_logs[top_index]["defect"]
top_score = boosted_scores[top_index]

# 5. print output
print(f"Similarity original score: {similarities.round(2)}")
print(f"Weighted score: {boosted_scores.round(2)}")
print(f"Suggested defect type: {top_defect} (Confidence: {top_score:.2f})")
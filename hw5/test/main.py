import pandas as pd

hw1 = "hw1.csv"
hw2 = "hw2.csv"
hw3 = "hw3.csv"
hw4 = "hw4.csv"

df1 = pd.read_csv(hw1)
df2 = pd.read_csv(hw2)
df3 = pd.read_csv(hw2)
df4 = pd.read_csv(hw3)


student_num = df1["Student ID"].tolist()

hw1_score = df1["Score1"].tolist()
hw2_score = df2["Score1"].tolist()
hw3_score = df3["Score1"].tolist()
hw4_score = df4["Score1"].tolist()


total_score = [hw1_score[i] + hw2_score[i] +
               hw3_score[i] + hw4_score[i] for i in range(0, len(hw1_score))]


lst = list(zip(total_score, student_num))

print(lst)
lst = sorted(lst)
for a in lst:
    print(a, "\n")

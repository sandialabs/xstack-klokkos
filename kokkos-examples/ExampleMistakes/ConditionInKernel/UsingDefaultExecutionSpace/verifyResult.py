

A = [10988.2,16235.3,10246.4,6232.96,6759.43,15596,13817.6,11972.6]
b = [14.0222,93.1132,8.1959,9.98256,88.9686,75.081,68.4533,63.2976]

print("results obtained using using i == 7 condition")
result = 0.0
for i in range(len(A)):
    if i == 7:
        b[(i+1)%len(b)] = b[i] - 1
    result = result + (A[i] * b[i])
print(result)


b = [14.0222,93.1132,8.1959,9.98256,88.9686,75.081,68.4533,63.2976]
print("results obtained using using i == 5 condition")
result = 0.0
for i in range(len(A)):
    if i == 5:
        b[(i+1)] = b[i%len(b)] - 1
    result = result + (A[i] * b[i])
print(result)




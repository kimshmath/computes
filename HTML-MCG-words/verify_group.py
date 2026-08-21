import time
import sys

def mat_mul(A, B):
    return [
        [sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
        for i in range(3)
    ]

def mat_eq(A, B):
    return all(A[i][j] == B[i][j] for i in range(3) for j in range(3))

def verify_conjecture(max_len):
    print(f"Verifying the free product conjecture up to word length {max_len}...")
    
    A = [
        [0, 0, 1],
        [-1, 0, -3],
        [0, -1, 0]
    ]
    B = [
        [-1, 0, -1],
        [1, -1, 3],
        [0, 1, -1]
    ]
    C = [
        [4, -3, -10],
        [-1, 1, 3],
        [-1, 1, 4]
    ]
    
    # 1. Verify that A and B commute (Z^2 property)
    if not mat_eq(mat_mul(A, B), mat_mul(B, A)):
        print("Error: A and B do not commute!")
        return

    # Function to compute exact inverse for a 3x3 integer matrix with det=1
    def exact_inv(M):
        minv = [[0]*3 for _ in range(3)]
        minv[0][0] = M[1][1]*M[2][2] - M[1][2]*M[2][1]
        minv[0][1] = M[0][2]*M[2][1] - M[0][1]*M[2][2]
        minv[0][2] = M[0][1]*M[1][2] - M[0][2]*M[1][1]
        minv[1][0] = M[1][2]*M[2][0] - M[1][0]*M[2][2]
        minv[1][1] = M[0][0]*M[2][2] - M[0][2]*M[2][0]
        minv[1][2] = M[0][2]*M[1][0] - M[0][0]*M[1][2]
        minv[2][0] = M[1][0]*M[2][1] - M[1][1]*M[2][0]
        minv[2][1] = M[0][1]*M[2][0] - M[0][0]*M[2][1]
        minv[2][2] = M[0][0]*M[1][1] - M[0][1]*M[1][0]
        return minv

    A_inv = exact_inv(A)
    B_inv = exact_inv(B)
    C_inv = exact_inv(C)
    
    I = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    
    # Precompute non-identity elements of Z^2 (A^i B^j)
    Z2_elements = []
    for i in range(-max_len, max_len + 1):
        for j in range(-max_len, max_len + 1):
            length = abs(i) + abs(j)
            if 0 < length <= max_len:
                M = I
                if i > 0:
                    for _ in range(i): M = mat_mul(M, A)
                elif i < 0:
                    for _ in range(-i): M = mat_mul(M, A_inv)
                if j > 0:
                    for _ in range(j): M = mat_mul(M, B)
                elif j < 0:
                    for _ in range(-j): M = mat_mul(M, B_inv)
                
                desc = ""
                if i != 0: desc += f"A^{i}" if i != 1 else "A"
                if j != 0: desc += f"B^{j}" if j != 1 else "B"
                Z2_elements.append((M, length, desc))

    # Precompute non-identity elements of Z (C^k)
    Z_elements = []
    for k in range(-max_len, max_len + 1):
        length = abs(k)
        if 0 < length <= max_len:
            M = I
            if k > 0:
                for _ in range(k): M = mat_mul(M, C)
            elif k < 0:
                for _ in range(-k): M = mat_mul(M, C_inv)
            desc = f"C^{k}" if k != 1 else "C"
            Z_elements.append((M, length, desc))
            
    words_checked = [0]
    start_time = time.time()
    
    # DFS to generate all alternating normal forms
    def dfs(current_M, current_len, last_group, path):
        if current_len > 0:
            words_checked[0] += 1
            if mat_eq(current_M, I):
                print(f"\nRELATION FOUND at length {current_len}!")
                print("Word:", " * ".join(path))
                return False
                
        # If the last block was not from Z2, append a block from Z2
        if last_group != 1:
            for M, l, desc in Z2_elements:
                if current_len + l <= max_len:
                    if not dfs(mat_mul(current_M, M), current_len + l, 1, path + [desc]):
                        return False
                        
        # If the last block was not from Z, append a block from Z
        if last_group != 2:
            for M, l, desc in Z_elements:
                if current_len + l <= max_len:
                    if not dfs(mat_mul(current_M, M), current_len + l, 2, path + [desc]):
                        return False
                        
        return True

    success = dfs(I, 0, 0, [])
    
    if success:
        elapsed = time.time() - start_time
        print(f"Verified successfully up to length {max_len}.")
        print(f"No non-trivial identity relation found.")
        print(f"Total words checked: {words_checked[0]}")
        print(f"Time elapsed: {elapsed:.2f} seconds")

if __name__ == '__main__':
    max_len = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    verify_conjecture(max_len)

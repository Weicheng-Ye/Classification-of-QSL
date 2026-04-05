import Z2TO
import Z4TO

def print_result_lengths(name, generate_func, actions, homotopylist):
    print(f"--- {name} ---")
    for action in actions:
        try:
            res = generate_func(action, homotopylist)
            lengths = [len(r) for r in res]
            print(f"Action {action}  homotopy: {homotopylist} -> lengths: {lengths}")
        except Exception as e:
            print(f"Action {action}  Error: {e}")

if __name__ == "__main__":
    h_p6m = ["0", "a", "c", "a+c"]
    h_p4m = ["0", "a", "b", "c", "a+b", "a+c", "b+c", "a+b+c"]

    print("Results for Z2TO:")
    print_result_lengths("p6mO3", Z2TO.p6mO3Generate, [1, 2, 3, 4, 5, 6, 7, 8], h_p6m)
    print_result_lengths("p6mZ2", Z2TO.p6mZ2Generate, [1, 2, 3, 4, 5, 6, 7, 8], h_p6m)
    print_result_lengths("p4mO3", Z2TO.p4mO3Generate, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], h_p4m)
    print_result_lengths("p4mZ2", Z2TO.p4mZ2Generate, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], h_p4m)

    print("Results for Z4TO:")
    print_result_lengths("p6mO3", Z4TO.p6mO3Generate, [1, 2, 3, 4], h_p6m)
    print_result_lengths("p6mZ2", Z4TO.p6mZ2Generate, [1, 2, 3, 4], h_p6m)
    print_result_lengths("p4mO3", Z4TO.p4mO3Generate, [1, 2, 3, 4, 5, 6, 7, 8], h_p4m)
    print_result_lengths("p4mZ2", Z4TO.p4mZ2Generate, [1, 2, 3, 4, 5, 6, 7, 8], h_p4m)

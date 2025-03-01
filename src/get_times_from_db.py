import os
os.environ['MPLBACKEND'] = 'Agg'
import sqlite3
import numpy as np
import matplotlib.pyplot as plt
# plt.use('Agg')  # Set to 'Agg' for non-GUI backends

data_dir = "/home/yizhou7/mariposa/data/dbs/"
total_sum = 0
elapsed_dict = {}
elapsed_times = []

for file_name in os.listdir(data_dir):
    if file_name.startswith("singleton_") and not file_name.endswith(".timeout"):
        base_path = os.path.join(data_dir, file_name, "base.z3")
        db_path = os.path.join(base_path, "verify.db")
        
        if os.path.exists(db_path):
            table_name = f"{file_name}_base_z3_z3_4_13_0_exp"
            query = f"SELECT SUM(elapsed_milli) FROM {table_name};"
            
            try:
                conn = sqlite3.connect(db_path)
                cursor = conn.cursor()
                cursor.execute(query)
                result = cursor.fetchone()
                conn.close()
                
                if result and result[0] is not None:
                    elapsed_time = result[0]
                    total_sum += elapsed_time
                    elapsed_dict[file_name] = elapsed_time
                    elapsed_times.append(elapsed_time)
            except sqlite3.Error as e:
                print(f"Error querying {db_path}: {e}")

print(f"Total Time: {total_sum} miliseconds")
print(f"Total Time: {total_sum / (1000)} seconds")
print(f"Total Time: {total_sum / (1000 * 60)} minutes")
print(f"Total Time: {total_sum / (1000 * 3600)} hours")
print("Elapsed Times:", elapsed_dict)



# Sort the data
sorted_data = np.sort(elapsed_times)

# Calculate the cumulative sum
cdf = np.arange(1, len(sorted_data) + 1) / len(sorted_data)

# Plot the CDF
plt.plot(sorted_data, cdf, marker='.', linestyle='none')
plt.xlabel('Value')
plt.ylabel('CDF')
plt.title('Cumulative Distribution Function')
plt.grid(True)
plt.show()
plt.savefig('cdf_plot.png')
import os
import random
'''
K = 2;
capacity =
  [60, 40, 45, 34, 60, 33, 34, 60];
  
N = 12;
nStudents = [500, 500, 750, 1000, 400, 450, 600, 350, 390, 420, 450, 500];
year = [1,2,3,2,3,2,1,1,3,2,3,1];

D = 3;
department = [1,2,3,3,2,2,3,1,3,1,2,3];

requiredTime = [40, 55, 50, 45, 45, 55, 55, 40, 40, 50, 55, 45];
'''

# With K = 8 we consider 8*4 = 32 different classrooms.
K = [2, 4, 6, 7, 8] 

for k in K:
	for it in range(20):
		n = random.randint(2*k, 8*k)
		
		capacity = [random.randint(30, 60) for i in range(4*k)]
		nStudents = [random.randint(300, 1200) for i in range(n)]
		year = [random.randint(1,3) for i in range(n)]
		d = 3
		department = [random.randint(1, d) for i in range(n)]
		requiredTime = [random.randint(40, 60) for i in range(n)]

		filename = "./test/K-{0}_{1}.dzn".format(k,it+1)
		f = open(filename, 'w')

		f.write('K = {0};\n'.format(k))
		f.write("capacity = {0};\n".format(capacity))
		f.write('N = {0};\n'.format(n))
		f.write('nStudents = {0};\n'.format(nStudents))
		f.write('year = {0};\n'.format(year))
		f.write('D = {0};\n'.format(d))
		f.write('department = {0};\n'.format(department))
		f.write('requiredTime = {0};\n'.format(requiredTime))

		f.close()
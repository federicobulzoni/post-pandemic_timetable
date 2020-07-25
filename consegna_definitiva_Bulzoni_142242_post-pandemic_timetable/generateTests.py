import os
import random


K = [1, 2] 
g = 4
maxN = 15
for k in K:
	for it in range(50):
		#n = g*k + it
		n = random.randint(g*k, maxN)
		
		capacity = [random.randint(30, 60) for i in range(g*k)]
		nStudents = [random.randint(50, 300) for i in range(n)]
		year = [random.randint(1,3) for i in range(n)]
		d = 3
		department = range(1,d+1) + [random.randint(1, d) for i in range(d+1,n+1)]
		requiredTime = [random.randint(40, 60) for i in range(n)]

		filename_mzn = "./mzn/test/K-{0}_{1}.dzn".format(k,it+1)
		filename_lp = "./asp/test/K-{0}_{1}.lp".format(k,it+1)
		f_mzn = open(filename_mzn, 'w')
		f_lp = open(filename_lp, 'w')

		f_mzn.write('K = {0};\n'.format(k))
		f_mzn.write("capacity = {0};\n".format(capacity))
		f_mzn.write('N = {0};\n'.format(n))
		f_mzn.write('nStudents = {0};\n'.format(nStudents))
		f_mzn.write('year = {0};\n'.format(year))
		f_mzn.write('D = {0};\n'.format(d))
		f_mzn.write('department = {0};\n'.format(department))
		f_mzn.write('requiredTime = {0};\n'.format(requiredTime))

		f_mzn.close()

		f_lp.write('#const k = {0}.\n'.format(k))
		for i in range(0,k*g):
			f_lp.write('capacity({0},{1}).\n'.format(i+1, capacity[i]))

		f_lp.write('#const n = {0}.\n'.format(n))
		f_lp.write('#const d = {0}.\n'.format(d))
		for i in range(0,n):
			f_lp.write('nStudents({0},{1}).\n'.format(i+1, nStudents[i]))
			f_lp.write('year({0},{1}).\n'.format(i+1, year[i]))
			f_lp.write('department({0},{1}).\n'.format(i+1, department[i]))
			f_lp.write('requiredTime({0},{1}).\n'.format(i+1, requiredTime[i]))

		f_lp.close()






















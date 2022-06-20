
#include <ilcplex/cplex.h>
#include <ctype.h>
#include <stdlib.h>
#include <string>
#include <sstream>
#include <math.h>
#include <vector>
#include <iostream>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <fstream>
#include <assert.h>
#include <map>
#include <stack>
#include <omp.h>


// Probably won't change
#define PRECISION 3
#define EPSILON 1E-5
#define CONSOLE_PRINT 0

#define NUM_THREADS 8 // change according to the machine used
#define NEIGHBORHOOD 4
#define MINGAP 0.005 // optimality gap (tolerance gap)

// Instance file
char* FILEtoOPEN;
int facilityLimit;
double investment_diff;
//double service_diff;

using namespace std;

// Declarations for functions in this program 
double GetPrecision(double value, double precision=PRECISION){return (floor((value * pow(10, precision) + 0.5)) / pow(10, precision));}


class instance{
public:
	// CPLEX pointers;
	CPXLPptr origProblem;
	CPXENVptr envOrigProblem;

	CPXLPptr apprxProblem;
	CPXENVptr envApprxProblem;

	int* numCover; // this is equal to the number of covering facilties for each customer
	int* numLevel; // this is equal to minimum of Nlevel and numCover[i]
	int** M; // facilities covering each i in the order of their preference E.g. M[i][0] is the most preferred facility that can cover customer i

	vector<double> failProb;
	vector<int> regionIndex; // region index of a facility
	vector<double> fixedCost; // fixed cost for opening facilities

	vector<int> customer_regionIndex;
	vector<double> objCost;
	vector<char> typeOfVar;

	double** serviceCost;

	int Ncust;
	int Nfac;
	int Nsubs; // number of subpartitions
	int Nlevel;
	int Nregions;
	int Ncust_regions;
	int NCol;

	int Q_min_index; //minimum investment among all facility regions
	int Q_max_index; // maximum investment among all facility regions

	vector < vector<int> > partition;

	// these 2 arrays are filled in the constructor
	unsigned int*** y_ind; 
	unsigned int*** w_ind;

	//unsigned int* F_min_index; // minimum customer service cost in a customer region index
	unsigned int* F_max_index; // maximum customer service cost in a customer region index

	double gini_eps;
	double gini;

	instance ()
	{
		gini_eps = 1.0;
		gini = 1.0;

		ifstream myfile;
		myfile.open(FILEtoOPEN); //change directory, if needed

		double tempd;
		int tempInt;
		
		myfile >> Ncust; // number of customers in the data set. 
		myfile >> Nfac; // number of facilities including dummy.
		myfile >> Nlevel;
		myfile >> Nregions;
		myfile >> Ncust_regions;

		myfile >> Nsubs; // number of subproblems in the customer partition
		partition.resize(Nsubs);

		for (int i=0; i<Nsubs; i++)
		{
			myfile >> tempInt;
			partition[i].resize(tempInt);
			for (int j=0; j<tempInt; j++)
				myfile >> partition[i][j];
		}
	
		numCover = new int [Ncust];
		numLevel = new int [Ncust]; 

		M = new int* [Ncust];
		serviceCost = new double* [Ncust];

		objCost.resize(Nfac,0.0);
		typeOfVar.resize(Nfac, 'B');

		fixedCost.resize(Nfac);
		failProb.resize(Nfac);
		regionIndex.resize(Nfac);

		for (int j = 0; j < Nfac ; j++)
		{
			myfile >> fixedCost[j]; // fixed cost for each facility (including emergency).
			myfile >> failProb[j]; 
			myfile >> regionIndex[j];
			failProb[j] = GetPrecision(failProb[j]);
		}

		customer_regionIndex.resize(Ncust);
		for (int i = 0; i < Ncust ; i++)
		{
			myfile >> customer_regionIndex[i];
			myfile >> numCover[i];
			numLevel[i] = (Nlevel<numCover[i])?Nlevel:numCover[i];

			M[i] = new int [numCover[i]]; // number of elements in M[i] = numCover[i]
			for (int j=0;j< numCover[i];j++)
				myfile >> M[i][j];

			serviceCost[i] = new double [numCover[i]];
			for (int j=0;j< numCover[i];j++)
				myfile >> serviceCost[i][j];
		}


		y_ind = new unsigned int** [Ncust];
		w_ind = new unsigned int**[Ncust];

		int indexCalc=Nfac;

		// fill in y_ind
		for (unsigned int i = 0; i<Ncust; i++)
		{
			y_ind[i] = new unsigned int*[numCover[i]];
			for (unsigned int j = 0; j<numCover[i]; j++)
			{
				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel; // facility of order j in the preference list of customer i cannot be assigned at level j+1 or greater
				y_ind[i][j] = new unsigned int[k];
				for (int r = 0; r<k; r++)
				{
					objCost.push_back(0);
					typeOfVar.push_back('C');

					y_ind[i][j][r] = indexCalc;
					indexCalc++;
				}
			}
		}

		// fill in w_ind
		for (unsigned int i=0; i<Ncust; i++)
		{
			w_ind[i] =  new unsigned int* [numCover[i]];
			for (unsigned int j=0; j<numCover[i]; j++)
			{
				unsigned int k = (j+1<Nlevel)?j+1:Nlevel; 
				w_ind[i][j] =  new unsigned int [k];
				for (int r=0; r<k; r++)
				{
					objCost.push_back(0);
					typeOfVar.push_back('C');

					w_ind[i][j][r] =  indexCalc;
					indexCalc++;
				}
			}
		}		

		// Q_min variable index
		objCost.push_back(0);
		typeOfVar.push_back('C');
		Q_min_index = indexCalc;
		indexCalc++;

		// Q_max variable index
		objCost.push_back(0);
		typeOfVar.push_back('C');
		Q_max_index = indexCalc;
		indexCalc++;

		// F_min_index = new unsigned int[Ncust_regions];
		F_max_index = new unsigned int[Ncust_regions];
		for (unsigned int i = 0; i < Ncust_regions; i++)
		{
			// objCost.push_back(0);
			// typeOfVar.push_back('C');
			// F_min_index[i] = indexCalc;
			// indexCalc++;

			objCost.push_back(1);
			typeOfVar.push_back('C');
			F_max_index[i] = indexCalc;
			indexCalc++;
		}

		NCol = indexCalc; // number of variables in the full problem
	}
	
	void generate_original_full_problem ()
	{
		int status;
		
		// vectors instead of CPLEX arrays 
		vector<int> rmatbeg;
		vector<int> rmatind;
		vector<double> rmatval;
		vector<double> rhs;
		vector<char> sense;

		int NUMNZ = 0; //initialize the non-zero elements counter...
		

		for (int i=0; i<Ncust;i++)
		{
			// constraints (2)
			for (int r = 0; r < numLevel[i] ; r++)
			{
				rmatbeg.push_back(NUMNZ);
				sense.push_back('E');
				rhs.push_back(1);

				for (int j = r; j < numCover[i]; j++){
					rmatind.push_back(y_ind[i][j][r]); //Y_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}

				for (int s=0; s < r; s++){
					rmatind.push_back(y_ind[i][numCover[i]-1][s]); //Y_iJs
					rmatval.push_back(1);
					NUMNZ++;
				}
			}
		
			// constraints (1g) 
			for (int j = 0; j < numCover[i] ; j++){
				rmatbeg.push_back(NUMNZ);
				sense.push_back('L');
				rhs.push_back(0);

				rmatind.push_back(M[i][j]);
				rmatval.push_back(-1);
				NUMNZ++;

				unsigned int k = (j+1<Nlevel)?j+1:Nlevel;
				for (int r = 0; r < k ; r++){	
					rmatind.push_back(y_ind[i][j][r]); 
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			//Constraint (1h)
			for (int r = 0; r < numLevel[i]-1; r++)
			{
				for (int m = r; m < numCover[i]-1; m++)
				{
					rmatbeg.push_back(NUMNZ);
					sense.push_back('G');
					rhs.push_back(-1);

					rmatind.push_back(M[i][m]); // -X_m
					rmatval.push_back(-1);
					NUMNZ++;

					for (int s = 0; s < r; s++)
					{
						rmatind.push_back(y_ind[i][m][s]); // Y_ims
						rmatval.push_back(1);
						NUMNZ++;
					}

					for (int j = m+1; j < numCover[i]; j++)
					{
						rmatind.push_back(y_ind[i][j][r]); // -Y_ijr
						rmatval.push_back(-1);
						NUMNZ++;
					}
				}
			}


			// constraints (1i)
			rmatbeg.push_back(NUMNZ);
			sense.push_back('E');
			rhs.push_back(1);

			for (int r = 0; r< numLevel[i]; r++)
			{
				rmatind.push_back(y_ind[i][numCover[i] - 1][r]); //Y_iJr
				rmatval.push_back(1);
				NUMNZ++;
			}

			// constraints (5b) 
			rmatbeg.push_back(NUMNZ);
			sense.push_back('E');
			rhs.push_back(1.0);
				
			for (int j = 0; j < numCover[i]; j++)
			{
				rmatind.push_back(w_ind[i][j][0]); //W_ij1
				rmatval.push_back(1);
				NUMNZ++;
			}
		
			// constraints (5c) 
			for (int r = 1; r < numLevel[i] ; r++)
			{
				rmatbeg.push_back(NUMNZ);
				sense.push_back('E');
				rhs.push_back(0);

				for (int j = r; j < numCover[i]; j++)
				{
					rmatind.push_back(w_ind[i][j][r]); //W_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}

				for (int k = r-1; k < numCover[i] ; k++)
				{
					rmatind.push_back(w_ind[i][k][r-1]); // W_ikr-1
					rmatval.push_back(-failProb[M[i][k]]);
					NUMNZ++;
				}
			}

			// constraints (5d) 
			for (int j = 0; j < numCover[i]; j++)
			{
				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r < k; r++)
				{
					rmatbeg.push_back(NUMNZ);
					sense.push_back('L');
					rhs.push_back(1);

					for (int k = r; k < numCover[i]; k++)
					{
						if (k != j)
						{
							rmatind.push_back(w_ind[i][k][r]); // W_ikr
							rmatval.push_back(1);
							NUMNZ++;
						}
					}

					rmatind.push_back(y_ind[i][j][r]); //Y_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			// customer min fairmess cosntraint within each customer region
			//rmatbeg.push_back(NUMNZ);
			//sense.push_back('G');
			//rhs.push_back(0);

			//rmatind.push_back(F_min_index[customer_regionIndex[i]]);
			//rmatval.push_back(-1);
			//NUMNZ++;

			//for (unsigned int j = 0; j<numCover[i]; j++)
			//{
			//	unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
			//	for (int r = 0; r<k; r++)
			//	{
			//		rmatind.push_back(w_ind[i][j][r]); // W_ijr
			//		rmatval.push_back(objCost[w_ind[i][j][r]]);
			//		NUMNZ++;
			//	}
			//}

			// customer max fairmess cosntraint within each customer region
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			rmatind.push_back(F_max_index[customer_regionIndex[i]]);
			rmatval.push_back(-1);
			NUMNZ++;

			for (unsigned int j = 0; j<numCover[i]; j++)
			{
				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r<k; r++)
				{
					rmatind.push_back(w_ind[i][j][r]); // W_ijr
					rmatval.push_back(serviceCost[i][j] * (1.0 - failProb[M[i][j]]));
					NUMNZ++;
				}
			}

		}

		//  Creating new environment and problem object *****
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(facilityLimit);
	
		// constraint (1b)
		for (int j = 0; j < Nfac; j++)
		{
			rmatind.push_back(j); //X_j
			rmatval.push_back(1);
			NUMNZ++;
		}


		// constraint (1c)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_max_index); //Q_max
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1d)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('G');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_min_index); //Q_min
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1e)
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(0);

		rmatind.push_back(Q_max_index); //Q_max
		rmatval.push_back(1.0- investment_diff);
		NUMNZ++;

		rmatind.push_back(Q_min_index); //Q_min
		rmatval.push_back(-1);
		NUMNZ++;

		// first stage fairness constraint or customers
		//for (unsigned int i = 0; i < Ncust_regions; i++)
		//{
		//	rmatbeg.push_back(NUMNZ);
		//	sense.push_back('L');
		//	rhs.push_back(0);

		//	rmatind.push_back(F_max_index[i]); //F_max
		//	rmatval.push_back(1.0 - service_diff);
		//	NUMNZ++;

		//	rmatind.push_back(F_min_index[i]); //F_min
		//	rmatval.push_back(-1);
		//	NUMNZ++;
		//}
		

		// Initialize the CPLEX environment (this is for the custProblem pointers)
		envOrigProblem = CPXopenCPLEX (&status);
	
		if ( envOrigProblem == NULL ) {
			cout << "generate_original_full_problem: could not open CPLEX environment" << endl;
			exit(0);
		}

		// Create the problem. 
		origProblem = CPXcreateprob (envOrigProblem, &status, "FacilityDistruption; original problem");
		if ( origProblem == NULL ) {
			cout << "generate_original_full_problem: could not create a new LP object" << endl;
			exit(0);
		}
	
		// Problem is minimization
		CPXchgobjsen (envOrigProblem, origProblem, CPX_MIN);

		// Creating columns
		status = CPXnewcols (envOrigProblem, origProblem, objCost.size(), &objCost.front(), NULL , NULL, &typeOfVar.front(), NULL);
	
		// adding rows
		status = CPXaddrows (envOrigProblem, origProblem, 0, rhs.size(), NUMNZ, &rhs.front(), &sense.front(), &rmatbeg.front(),
						&rmatind.front(), &rmatval.front(), NULL, NULL);
		if ( status ) {
			cout << "generate_original_full_problem: could not add rows" << endl;
			exit(0);
		}


		stringstream ss;
		string outputFile;
		ss << "full_" ;
		ss << FILEtoOPEN << ".lp";
		ss >> outputFile;

		status = CPXwriteprob (envOrigProblem, origProblem, outputFile.c_str(), NULL);

	}

	void generate_original_full_problem_accomodate_preference(int k_level, double alpha_level)
	{
		int status;

		// vectors instead of CPLEX arrays 
		vector<int> rmatbeg;
		vector<int> rmatind;
		vector<double> rmatval;
		vector<double> rhs;
		vector<char> sense;

		int NUMNZ = 0; //initialize the non-zero elements counter...


		for (int i = 0; i<Ncust; i++)
		{
			// s_i - \sum_{j \in J_ik}X_j <= 0
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			rmatind.push_back(NCol + i); //s_i
			rmatval.push_back(1);
			NUMNZ++;

			int upto = k_level;
			if (upto > numCover[i])
				upto = numCover[i];

			for (int j = 0; j < upto; j++)
			{
				rmatind.push_back(M[i][j]);
				rmatval.push_back(-1);
				NUMNZ++;
			}

			// constraints (2)
			for (int r = 0; r < numLevel[i]; r++)
			{
				rmatbeg.push_back(NUMNZ);
				sense.push_back('E');
				rhs.push_back(1);

				for (int j = r; j < numCover[i]; j++) {
					rmatind.push_back(y_ind[i][j][r]); //Y_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}

				for (int s = 0; s < r; s++) {
					rmatind.push_back(y_ind[i][numCover[i] - 1][s]); //Y_iJs
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			// constraints (1g) 
			for (int j = 0; j < numCover[i]; j++) {
				rmatbeg.push_back(NUMNZ);
				sense.push_back('L');
				rhs.push_back(0);

				rmatind.push_back(M[i][j]);
				rmatval.push_back(-1);
				NUMNZ++;

				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r < k; r++) {
					rmatind.push_back(y_ind[i][j][r]);
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			//Constraint (1h)
			for (int r = 0; r < numLevel[i] - 1; r++)
			{
				for (int m = r; m < numCover[i] - 1; m++)
				{
					rmatbeg.push_back(NUMNZ);
					sense.push_back('G');
					rhs.push_back(-1);

					rmatind.push_back(M[i][m]); // -X_m
					rmatval.push_back(-1);
					NUMNZ++;

					for (int s = 0; s < r; s++)
					{
						rmatind.push_back(y_ind[i][m][s]); // Y_ims
						rmatval.push_back(1);
						NUMNZ++;
					}

					for (int j = m + 1; j < numCover[i]; j++)
					{
						rmatind.push_back(y_ind[i][j][r]); // -Y_ijr
						rmatval.push_back(-1);
						NUMNZ++;
					}
				}
			}


			// constraints (1i)
			rmatbeg.push_back(NUMNZ);
			sense.push_back('E');
			rhs.push_back(1);

			for (int r = 0; r< numLevel[i]; r++)
			{
				rmatind.push_back(y_ind[i][numCover[i] - 1][r]); //Y_iJr
				rmatval.push_back(1);
				NUMNZ++;
			}

			// constraints (5b) 
			rmatbeg.push_back(NUMNZ);
			sense.push_back('E');
			rhs.push_back(1.0);

			for (int j = 0; j < numCover[i]; j++)
			{
				rmatind.push_back(w_ind[i][j][0]); //W_ij1
				rmatval.push_back(1);
				NUMNZ++;
			}

			// constraints (5c) 
			for (int r = 1; r < numLevel[i]; r++)
			{
				rmatbeg.push_back(NUMNZ);
				sense.push_back('E');
				rhs.push_back(0);

				for (int j = r; j < numCover[i]; j++)
				{
					rmatind.push_back(w_ind[i][j][r]); //W_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}

				for (int k = r - 1; k < numCover[i]; k++)
				{
					rmatind.push_back(w_ind[i][k][r - 1]); // W_ikr-1
					rmatval.push_back(-failProb[M[i][k]]);
					NUMNZ++;
				}
			}

			// constraints (5d) 
			for (int j = 0; j < numCover[i]; j++)
			{
				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r < k; r++)
				{
					rmatbeg.push_back(NUMNZ);
					sense.push_back('L');
					rhs.push_back(1);

					for (int k = r; k < numCover[i]; k++)
					{
						if (k != j)
						{
							rmatind.push_back(w_ind[i][k][r]); // W_ikr
							rmatval.push_back(1);
							NUMNZ++;
						}
					}

					rmatind.push_back(y_ind[i][j][r]); //Y_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}
			}
		}

		///////////////////////////////////////////////
		rmatbeg.push_back(NUMNZ);
		sense.push_back('G');
		rhs.push_back(alpha_level*Ncust);
		for (int i = 0; i<Ncust; i++)
		{
			rmatind.push_back(NCol + i); // s_i
			rmatval.push_back(1);

			NUMNZ++;

			objCost.push_back(0.0);
			typeOfVar.push_back('B');
		}
		///////////////////////////////////////////////////


		//  Creating new environment and problem object *****
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(facilityLimit);

		// constraint (1b)
		for (int j = 0; j < Nfac; j++)
		{
			rmatind.push_back(j); //X_j
			rmatval.push_back(1);
			NUMNZ++;
		}


		// constraint (1c)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_max_index); //Q_max
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1d)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('G');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_min_index); //Q_min
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1e)
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(0);

		rmatind.push_back(Q_max_index); //Q_max
		rmatval.push_back(1.0 - investment_diff);
		NUMNZ++;

		rmatind.push_back(Q_min_index); //Q_min
		rmatval.push_back(-1);
		NUMNZ++;


		// Initialize the CPLEX environment (this is for the custProblem pointers)
		envOrigProblem = CPXopenCPLEX(&status);

		if (envOrigProblem == NULL) {
			cout << "generate_original_full_problem: could not open CPLEX environment" << endl;
			exit(0);
		}

		// Create the problem. 
		origProblem = CPXcreateprob(envOrigProblem, &status, "FacilityDistruption; original problem");
		if (origProblem == NULL) {
			cout << "generate_original_full_problem: could not create a new LP object" << endl;
			exit(0);
		}

		// Problem is minimization
		CPXchgobjsen(envOrigProblem, origProblem, CPX_MIN);

		// Creating columns
		status = CPXnewcols(envOrigProblem, origProblem, objCost.size(), &objCost.front(), NULL, NULL, &typeOfVar.front(), NULL);

		// adding rows
		status = CPXaddrows(envOrigProblem, origProblem, 0, rhs.size(), NUMNZ, &rhs.front(), &sense.front(), &rmatbeg.front(),
			&rmatind.front(), &rmatval.front(), NULL, NULL);
		if (status) {
			cout << "generate_original_full_problem: could not add rows" << endl;
			exit(0);
		}


		stringstream ss;
		string outputFile;
		ss << "preference-";
		ss << k_level << "-";
		ss << alpha_level << "-";
		ss << FILEtoOPEN << ".lp";
		ss >> outputFile;

		status = CPXwriteprob(envOrigProblem, origProblem, outputFile.c_str(), NULL);

	}

	double calculate_gini(double* x, int is_print=0)
	{
		vector<double> phi_ind(Ncust);

		double gini_nom = 0.0;
		double gini_denom = 0.0;

		for (int i = 0; i < Ncust; i++)
		{
			phi_ind[i] = 0.0;

			double prob = 0.0;

			for (int r = 0; r < numLevel[i]; r++)
			{
				phi_ind[i] += x[w_ind[i][numCover[i] - 1][r]] * serviceCost[i][numCover[i] - 1]; //w_iJr - multiplied with obj
				prob += x[w_ind[i][numCover[i] - 1][r]];
			}

			for (int j = 0; j < i; j++)
				gini_nom += abs(phi_ind[i] - phi_ind[j]);

			gini_denom += phi_ind[i];

			if (is_print == 1)
				cout << i << "\t" <<  phi_ind[i] << "\t" << prob << endl;

		}

		double gini = gini_nom / ((double)Ncust*gini_denom);
		return gini;
	}

	int create_annotation_original_problem()
	{
		int status = 0;

		int anno_idx;

		vector<CPXLONG> benders_partition;
		vector<int> colidx;

		/* Create benders annotation */
		status = CPXnewlongannotation(envOrigProblem, origProblem, CPX_BENDERS_ANNOTATION, CPX_BENDERS_MASTERVALUE);
		if (status) {
			fprintf(stderr, "Could not create benders annotation.\n");
			exit(0);
		}

		/* Query benders annotation index */
		status = CPXgetlongannotationindex(envOrigProblem, origProblem, CPX_BENDERS_ANNOTATION, &anno_idx);
		if (status) {
			fprintf(stderr, "Could not retrieve benders annotation index.\n");
			exit(0);
		}


		/* benders partition for y and w variables, they are in the subproblems */
		for (int m = 0; m<Nsubs; m++)
		{
			int partsize = partition[m].size();
			for (int l = 0; l<partsize; l++)
			{
				int i = partition[m][l];

				for (unsigned int j = 0; j < numCover[i]; j++)
				{
					unsigned int k = (j + 1 < Nlevel) ? j + 1 : Nlevel;
					for (unsigned int r = 0; r < k; r++)
					{
						benders_partition.push_back(CPX_BENDERS_MASTERVALUE + 1 + m);
						colidx.push_back(y_ind[i][j][r]);

						benders_partition.push_back(CPX_BENDERS_MASTERVALUE + 1 + m);
						colidx.push_back(w_ind[i][j][r]);
					}
				}
			}
		}


		/* set annotation values */
		status = CPXsetlongannotations(envOrigProblem, origProblem, anno_idx, CPX_ANNOTATIONOBJ_COL, colidx.size(), &colidx.front(), &benders_partition.front());
		if (status) {
			fprintf(stderr, "Could not set benders annotation.\n");
			exit(0);
		}

		return (status);

	} /* END create_annotation */

	void update_approx_fullProblem(vector<double>& upper_bound, vector < vector< vector<double> > >& Qijr)
	{
		// calculate Q_ijr
		Qijr.resize(Ncust);

		for (int i = 0; i<Ncust; i++)
		{
			Qijr[i].resize(numCover[i]);

			for (int j = 0; j < numCover[i]; j++)
			{
				vector<double> sorted_failProb;

				for (int l = 0; l<j; l++)
				{
					if (upper_bound[M[i][l]] >= 1 - EPSILON)
						sorted_failProb.push_back(failProb[M[i][l]]);
				}

				sort(sorted_failProb.begin(), sorted_failProb.end());

				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;

				Qijr[i][j].resize(k);

				for (int r = 0; r < k; r++)
				{
					if ((upper_bound[M[i][j]] <= EPSILON) || (sorted_failProb.size() < r))
					{
						Qijr[i][j][r] = 0;
					}
					else
					{
						Qijr[i][j][r] = 1.0;

						for (int l = 0; l<r; l++)
							Qijr[i][j][r] = Qijr[i][j][r] * sorted_failProb[l];
					}

					Qijr[i][j][r] = Qijr[i][j][r] * (1.0 - failProb[M[i][j]]); // 1.0-failProb[M[i][j]] the jth facility does not fail at level r is included in the objCost
				}
			}
		}
	}

	void generate_approx_full_problem()
	{
		int status;

		// vectors instead of CPLEX arrays 
		vector<int> rmatbeg;
		vector<int> rmatind;
		vector<double> rmatval;
		vector<double> rhs;
		vector<char> sense;

		int NUMNZ = 0; //initialize the non-zero elements counter...

		vector<double> upper_bound(Nfac, 1.0);
		vector < vector< vector<double> > > Qijr;
		update_approx_fullProblem(upper_bound, Qijr);


		for (int i = 0; i<Ncust; i++)
		{
			// constraints (2)
			for (int r = 0; r < numLevel[i]; r++)
			{
				rmatbeg.push_back(NUMNZ);
				sense.push_back('E');
				rhs.push_back(1);

				for (int j = r; j < numCover[i]; j++) {
					rmatind.push_back(y_ind[i][j][r]); //Y_ijr
					rmatval.push_back(1);
					NUMNZ++;
				}

				for (int s = 0; s < r; s++) {
					rmatind.push_back(y_ind[i][numCover[i] - 1][s]); //Y_iJs
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			// constraints (1g) 
			for (int j = 0; j < numCover[i]; j++) {
				rmatbeg.push_back(NUMNZ);
				sense.push_back('L');
				rhs.push_back(0);

				rmatind.push_back(M[i][j]);
				rmatval.push_back(-1);
				NUMNZ++;

				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r < k; r++) {
					rmatind.push_back(y_ind[i][j][r]);
					rmatval.push_back(1);
					NUMNZ++;
				}
			}

			//Constraint (1h)
			for (int r = 0; r < numLevel[i] - 1; r++)
			{
				for (int m = r; m < numCover[i] - 1; m++)
				{
					rmatbeg.push_back(NUMNZ);
					sense.push_back('G');
					rhs.push_back(-1);

					rmatind.push_back(M[i][m]); // -X_m
					rmatval.push_back(-1);
					NUMNZ++;

					for (int s = 0; s < r; s++)
					{
						rmatind.push_back(y_ind[i][m][s]); // Y_ims
						rmatval.push_back(1);
						NUMNZ++;
					}

					for (int j = m + 1; j < numCover[i]; j++)
					{
						rmatind.push_back(y_ind[i][j][r]); // -Y_ijr
						rmatval.push_back(-1);
						NUMNZ++;
					}
				}
			}


			// constraints (1i)
			rmatbeg.push_back(NUMNZ);
			sense.push_back('E');
			rhs.push_back(1);

			for (int r = 0; r< numLevel[i]; r++)
			{
				rmatind.push_back(y_ind[i][numCover[i] - 1][r]); //Y_iJr
				rmatval.push_back(1);
				NUMNZ++;
			}


			// customer max fairmess cosntraint within each customer region
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			rmatind.push_back(F_max_index[customer_regionIndex[i]]);
			rmatval.push_back(-1);
			NUMNZ++;

			for (unsigned int j = 0; j<numCover[i]; j++)
			{
				unsigned int k = (j + 1<Nlevel) ? j + 1 : Nlevel;
				for (int r = 0; r<k; r++)
				{
					rmatind.push_back(y_ind[i][j][r]); // Y_ijr
					rmatval.push_back(serviceCost[i][j] * Qijr[i][j][r]);
					NUMNZ++;
				}
			}

		}

		//  Creating new environment and problem object *****
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(facilityLimit);

		// constraint (1b)
		for (int j = 0; j < Nfac; j++)
		{
			rmatind.push_back(j); //X_j
			rmatval.push_back(1);
			NUMNZ++;
		}


		// constraint (1c)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('L');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_max_index); //Q_max
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1d)
		for (int v = 0; v < Nregions; v++)
		{
			rmatbeg.push_back(NUMNZ);
			sense.push_back('G');
			rhs.push_back(0);

			for (int j = 0; j < Nfac; j++)
			{
				if (regionIndex[j] == v)
				{
					rmatind.push_back(j); //X_j
					rmatval.push_back(fixedCost[j]);
					NUMNZ++;
				}
			}

			rmatind.push_back(Q_min_index); //Q_min
			rmatval.push_back(-1);
			NUMNZ++;
		}

		// constraint (1e)
		rmatbeg.push_back(NUMNZ);
		sense.push_back('L');
		rhs.push_back(0);

		rmatind.push_back(Q_max_index); //Q_max
		rmatval.push_back(1.0 - investment_diff);
		NUMNZ++;

		rmatind.push_back(Q_min_index); //Q_min
		rmatval.push_back(-1);
		NUMNZ++;

		// Initialize the CPLEX environment (this is for the custProblem pointers)
		envApprxProblem = CPXopenCPLEX(&status);

		if (envApprxProblem == NULL) {
			cout << "generate_apprx_full_problem: could not open CPLEX environment" << endl;
			exit(0);
		}

		// Create the problem. 
		apprxProblem = CPXcreateprob(envApprxProblem, &status, "FacilityDistruption; apprx problem");
		if (apprxProblem == NULL) {
			cout << "generate_apprx_full_problem: could not create a new LP object" << endl;
			exit(0);
		}

		// Problem is minimization
		CPXchgobjsen(envApprxProblem, apprxProblem, CPX_MIN);

		// Creating columns
		status = CPXnewcols(envApprxProblem, apprxProblem, objCost.size(), &objCost.front(), NULL, NULL, &typeOfVar.front(), NULL);

		// adding rows
		status = CPXaddrows(envApprxProblem, apprxProblem, 0, rhs.size(), NUMNZ, &rhs.front(), &sense.front(), &rmatbeg.front(),
			&rmatind.front(), &rmatval.front(), NULL, NULL);
		if (status) {
			cout << "generate_apprx_full_problem: could not add rows" << endl;
			exit(0);
		}


		stringstream ss;
		string outputFile;
		ss << "approximate_";
		ss << FILEtoOPEN << ".lp";
		ss >> outputFile;

		status = CPXwriteprob(envApprxProblem, apprxProblem, outputFile.c_str(), NULL);

	}

	int create_annotation_approx_problem()
	{
		int status = 0;

		int anno_idx;

		vector<CPXLONG> benders_partition;
		vector<int> colidx;

		/* Create benders annotation */
		status = CPXnewlongannotation(envApprxProblem, apprxProblem, CPX_BENDERS_ANNOTATION, CPX_BENDERS_MASTERVALUE);
		if (status) {
			fprintf(stderr, "Could not create benders annotation.\n");
			exit(0);
		}

		/* Query benders annotation index */
		status = CPXgetlongannotationindex(envApprxProblem, apprxProblem, CPX_BENDERS_ANNOTATION, &anno_idx);
		if (status) {
			fprintf(stderr, "Could not retrieve benders annotation index.\n");
			exit(0);
		}


		/* benders partition for y variables, they are in the subproblems */
		for (int m = 0; m<Nsubs; m++)
		{
			int partsize = partition[m].size();
			for (int l = 0; l<partsize; l++)
			{
				int i = partition[m][l];

				for (unsigned int j = 0; j < numCover[i]; j++)
				{
					unsigned int k = (j + 1 < Nlevel) ? j + 1 : Nlevel;
					for (unsigned int r = 0; r < k; r++)
					{
						benders_partition.push_back(CPX_BENDERS_MASTERVALUE + 1 + m);
						colidx.push_back(y_ind[i][j][r]);
					}
				}
			}
		}


		/* set annotation values */
		status = CPXsetlongannotations(envApprxProblem, apprxProblem, anno_idx, CPX_ANNOTATIONOBJ_COL, colidx.size(), &colidx.front(), &benders_partition.front());
		if (status) {
			fprintf(stderr, "Could not set benders annotation.\n");
			exit(0);
		}

		return (status);

	} /* END create_annotation */
} ;

void heuristic_solution(instance* mydata, vector<double>& Xk, unsigned int num_solns, double& best_upper_bound, vector<double>& best_solution)
{
	for (int k = 0; k<num_solns; k++)
	{
		
		vector <double> F_max(mydata->Ncust_regions, 0.0);

		for (int i = 0; i<mydata->Ncust; i++)
		{
			double custobj = 0.0;

			vector<int> yr(mydata->Nlevel, -1);
			vector<int> lr(mydata->Nlevel, -1);
			vector<double> pr(mydata->Nlevel, 1);

			int r = 0;
			for (int j = 0; j<mydata->numCover[i] - 1 && r<mydata->Nlevel - 1; j++)
			{
				if (Xk[mydata->Nfac*k + mydata->M[i][j]] > 1 - EPSILON && j >= r)
				{
					yr[r] = mydata->M[i][j];
					lr[r] = j;
					if (r == 0)
						pr[r] = 1.0;
					else
						pr[r] = pr[r - 1] * mydata->failProb[yr[r - 1]];
					r++;
				}
			}

			// emergency facility
			yr[r] = mydata->Nfac - 1;
			lr[r] = mydata->numCover[i] - 1;
			if (r == 0)
				pr[r] = 1.0;
			else
				pr[r] = pr[r - 1] * mydata->failProb[yr[r - 1]];

			for (r = 0; r<mydata->Nlevel && yr[r] >= 0; r++)
			{
				custobj += mydata->serviceCost[i][lr[r]] * (1.0 - mydata->failProb[mydata->M[i][lr[r]]]) * pr[r];
				//cout << i << "\t" << lr[r] << "\t" << r << "\t" << mydata.w_ind[i][lr[r]][r]+1 << "\t" << pr[r] << endl;
			}

			F_max[mydata->customer_regionIndex[i]] = max(F_max[mydata->customer_regionIndex[i]], custobj);
		}

		double objval = 0.0;
		for (int i = 0; i < mydata->Ncust_regions; i++) { objval += F_max[i]; }


		if (objval < best_upper_bound || best_upper_bound <= 0.0)
		{
			best_upper_bound = objval;
			for (int j = 0; j<mydata->Nfac; j++) { best_solution[j] = Xk[mydata->Nfac*k + j]; /*cout << best_solution[j] << " ";*/ }
			//cout << endl;

			// cout << num_open << "\t" << facility_cost/best_upper_bound << "\t" << best_upper_bound << " *********** (incumbent Heuristic) \n";
		}
	}
}

void NeighborhoodSearch(instance* mydata, vector<double>& X, double& best_upper_bound, vector<double>& best_solution)
{
	heuristic_solution(mydata, X, 1, best_upper_bound, best_solution);

	double initial_obj_value = best_upper_bound;

	int N = mydata->Nfac - 1;

	for (int K = 1; K <= NEIGHBORHOOD; K++)
	{
		vector<int> bitmask(K, 1); // K leading 1's
		bitmask.resize(N, 0); // the last facility is the emergency facility and it is always open

							  // permute bitmask
		do {

			vector<double> Xcopy = X;

			int total_facility = 0;

			for (int i = 0; i < N; ++i) // [0..N-1] integers
			{
				if (bitmask[i])
					Xcopy[i] = 1 - Xcopy[i];

				total_facility += Xcopy[i];
			}

			if (total_facility <= facilityLimit)
			{
				vector <double> inv_facility_in_region(mydata->Nregions, 0);
				for (int i = 0; i < mydata->Nfac; i++)
					inv_facility_in_region[mydata->regionIndex[i]] += mydata->fixedCost[i] * Xcopy[i];

				double Qmax = inv_facility_in_region[0];
				double Qmin = inv_facility_in_region[0];

				for (int i = 1; i < mydata->Nregions; i++)
				{
					if (Qmax < inv_facility_in_region[i])
						Qmax = inv_facility_in_region[i];

					if (Qmin > inv_facility_in_region[i])
						Qmin = inv_facility_in_region[i];
				}

				if (Qmax-Qmin <= Qmax*investment_diff)
					heuristic_solution(mydata, Xcopy, 1, best_upper_bound, best_solution);
			}

		} while (std::prev_permutation(bitmask.begin(), bitmask.end()));
	}

	if (initial_obj_value > best_upper_bound)
		NeighborhoodSearch(mydata, best_solution, best_upper_bound, best_solution);
}


int main (int argc, char* argv[])
{
	FILEtoOPEN = argv[1];
	facilityLimit = atoi(argv[2]); // number of facilities to open
	investment_diff = atoi(argv[3])/100.0;
	//service_diff = atoi(argv[4]) / 100.0;
	int timeLimit = atoi(argv[4]);
	int benders_strategy = atoi(argv[5]); // 1: user annotation 3: automatic annotation 0: no benders, branch and bound

	cout << "Problem: " << FILEtoOPEN << "\tTime Limit: " << timeLimit << "\tInvestment Diff: " << investment_diff << "\tNum of Facility: " << facilityLimit << "\tBenders_strategy: " << benders_strategy << endl;
	
	instance mydata;

	cout << "Q-min-index: " << mydata.Q_min_index << endl;
	cout << "Q-max-index: " << mydata.Q_max_index << endl;

	for (unsigned int i = 0; i < mydata.Ncust_regions; i++)
	{
		//cout << "F_min_index[" << i << "]: " << mydata.F_min_index[i] << "\t";
		cout << "F_max_index[" << i << "]: " << mydata.F_max_index[i] << endl;
	}

	time_t start_time=time(NULL);


	double best_upper_bound, best_lower_bound, mipgap;
	int status, lpstat, nodecount;
	vector<double> x;

	if (benders_strategy == -2) // read in x solution from a file and test neighborhood search
	{
		char* FILEtoX = argv[6];
		ifstream myfileX;

		myfileX.open(FILEtoX); //change directory, if needed
		x.resize(mydata.Nfac);
		for (int j = 0; j< mydata.Nfac; j++) { myfileX >> x[j]; }
		myfileX >> best_lower_bound;
		best_upper_bound = -1; // initialize
		NeighborhoodSearch(&mydata, x, best_upper_bound, x);
		mipgap = 100 * (best_upper_bound - best_lower_bound) / best_lower_bound;
	}


	if (benders_strategy == -1) // custom annotation and solve the approximate problem
	{
		mydata.generate_approx_full_problem();

		status = CPXsetintparam(mydata.envApprxProblem, CPXPARAM_ScreenOutput, CPX_ON);
		status = CPXsetintparam(mydata.envApprxProblem, CPX_PARAM_THREADS, NUM_THREADS);
		status = CPXsetdblparam(mydata.envApprxProblem, CPX_PARAM_TILIM, timeLimit);

		mydata.create_annotation_approx_problem();
		status = CPXsetintparam(mydata.envApprxProblem, CPXPARAM_Benders_Strategy, 1);
		status = CPXbendersopt(mydata.envApprxProblem, mydata.apprxProblem);

		lpstat = CPXgetstat(mydata.envApprxProblem, mydata.apprxProblem);
		CPXgetbestobjval(mydata.envApprxProblem, mydata.apprxProblem, &best_lower_bound);
//		CPXgetobjval(mydata.envApprxProblem, mydata.apprxProblem, &best_upper_bound);
//		CPXgetmiprelgap(mydata.envApprxProblem, mydata.apprxProblem, &mipgap);

		x.resize(CPXgetnumcols(mydata.envApprxProblem, mydata.apprxProblem));
		CPXgetx(mydata.envApprxProblem, mydata.apprxProblem, &x.front(), 0, x.size() - 1);
		nodecount = CPXgetnodecnt(mydata.envApprxProblem, mydata.apprxProblem);

		// calculate heuristic upper bound using NeighborhoodSearch
		vector<double> X(mydata.Nfac);
		for (int j = 0; j< mydata.Nfac; j++) { X[j] = x[j]; }
		best_upper_bound = -1; // initialize
		NeighborhoodSearch(&mydata, X, best_upper_bound, x);
		mipgap = 100 * (best_upper_bound - best_lower_bound) / best_lower_bound;

		// calculate heuristic upper bound using the solution of the approx problem
		//mydata.generate_original_full_problem();
		//status = CPXchgprobtype(mydata.envOrigProblem, mydata.origProblem, CPXPROB_LP);
		//vector<int> bdsIndices(mydata.Nfac); vector <char> bothboundchar(mydata.Nfac,'B');
		//for (int j = 0; j< mydata.Nfac; j++) {bdsIndices[j]=j;}
		//status = CPXtightenbds(mydata.envOrigProblem, mydata.origProblem, mydata.Nfac, &bdsIndices.front(), &bothboundchar.front(), &x.front());
		//status = CPXlpopt(mydata.envOrigProblem, mydata.origProblem);
		//CPXgetobjval(mydata.envOrigProblem, mydata.origProblem, &best_upper_bound);
		//mipgap = 100*(best_upper_bound- best_lower_bound)/ best_lower_bound;

	}

	if (benders_strategy == 0) // no benders but still solve the original MIP
	{
		mydata.generate_original_full_problem();

		status = CPXsetintparam(mydata.envOrigProblem, CPXPARAM_ScreenOutput, CPX_ON);
		status = CPXsetintparam(mydata.envOrigProblem, CPX_PARAM_THREADS, NUM_THREADS);
		status = CPXsetdblparam(mydata.envOrigProblem, CPX_PARAM_TILIM, timeLimit);

		status = CPXmipopt(mydata.envOrigProblem, mydata.origProblem);

		lpstat = CPXgetstat(mydata.envOrigProblem, mydata.origProblem);
		CPXgetbestobjval(mydata.envOrigProblem, mydata.origProblem, &best_lower_bound);
		CPXgetobjval(mydata.envOrigProblem, mydata.origProblem, &best_upper_bound);
		CPXgetmiprelgap(mydata.envOrigProblem, mydata.origProblem, &mipgap);

		x.resize(CPXgetnumcols(mydata.envOrigProblem, mydata.origProblem));
		CPXgetx(mydata.envOrigProblem, mydata.origProblem, &x.front(), 0, x.size() - 1);
		nodecount = CPXgetnodecnt(mydata.envOrigProblem, mydata.origProblem);
	}

	if (benders_strategy == 1) // custom annotation
	{
		mydata.generate_original_full_problem();

		status = CPXsetintparam(mydata.envOrigProblem, CPXPARAM_ScreenOutput, CPX_ON);
		status = CPXsetintparam(mydata.envOrigProblem, CPX_PARAM_THREADS, NUM_THREADS);
		status = CPXsetdblparam(mydata.envOrigProblem, CPX_PARAM_TILIM, timeLimit);

		mydata.create_annotation_original_problem();
		status = CPXsetintparam(mydata.envOrigProblem, CPXPARAM_Benders_Strategy, benders_strategy);
		status = CPXbendersopt(mydata.envOrigProblem, mydata.origProblem);
		//CPXwriteannotations(mydata.envOrigProblem, mydata.origProblem, "benders-custom.ann");

		lpstat = CPXgetstat(mydata.envOrigProblem, mydata.origProblem);
		CPXgetbestobjval(mydata.envOrigProblem, mydata.origProblem, &best_lower_bound);
		CPXgetobjval(mydata.envOrigProblem, mydata.origProblem, &best_upper_bound);
		CPXgetmiprelgap(mydata.envOrigProblem, mydata.origProblem, &mipgap);

		x.resize(CPXgetnumcols(mydata.envOrigProblem, mydata.origProblem));
		CPXgetx(mydata.envOrigProblem, mydata.origProblem, &x.front(), 0, x.size() - 1);
		nodecount = CPXgetnodecnt(mydata.envOrigProblem, mydata.origProblem);
	}

	if (benders_strategy == 3) // full annotation
	{
		mydata.generate_original_full_problem();

		status = CPXsetintparam(mydata.envOrigProblem, CPXPARAM_ScreenOutput, CPX_ON);
		status = CPXsetintparam(mydata.envOrigProblem, CPX_PARAM_THREADS, NUM_THREADS);
		status = CPXsetdblparam(mydata.envOrigProblem, CPX_PARAM_TILIM, timeLimit);

		status = CPXsetintparam(mydata.envOrigProblem, CPXPARAM_Benders_Strategy, benders_strategy);
		status = CPXbendersopt(mydata.envOrigProblem, mydata.origProblem);
		//status = CPXwritebendersannotation(mydata.envOrigProblem, mydata.origProblem, "benders-full.ann");

		lpstat = CPXgetstat(mydata.envOrigProblem, mydata.origProblem);
		CPXgetbestobjval(mydata.envOrigProblem, mydata.origProblem, &best_lower_bound);
		CPXgetobjval(mydata.envOrigProblem, mydata.origProblem, &best_upper_bound);
		CPXgetmiprelgap(mydata.envOrigProblem, mydata.origProblem, &mipgap);

		x.resize(CPXgetnumcols(mydata.envOrigProblem, mydata.origProblem));
		CPXgetx(mydata.envOrigProblem, mydata.origProblem, &x.front(), 0, x.size() - 1);
		nodecount = CPXgetnodecnt(mydata.envOrigProblem, mydata.origProblem);
	}
	
	cout << "status: "      << lpstat           << endl;
	cout << "node count: "  << nodecount        << endl;
	cout << "upper_bound: " << best_upper_bound << endl;
	cout << "lower_bound: " << best_lower_bound << endl;
	cout << "Q_min: x[" << mydata.Q_min_index << "] " << x[mydata.Q_min_index] << endl;
	cout << "Q_max: x[" << mydata.Q_max_index << "] " << x[mydata.Q_max_index] << endl;
	cout << "Gini: " << mydata.calculate_gini(&x.front(), 0) << endl;
	cout << "mip_gap: "     << mipgap           << endl;
	cout << "total time: "  << difftime(time(NULL), start_time) << endl;

	vector <int> num_facility_in_region(mydata.Nregions,0);
	vector <double> inv_facility_in_region(mydata.Nregions, 0);

	int total_open_facility = 0;

	for (int i = 0; i < mydata.Nfac; i++)
	{
		cout << "x[" << i << "] " << x[i] << endl;
		total_open_facility += x[i];
		num_facility_in_region[mydata.regionIndex[i]] += x[i];
		inv_facility_in_region[mydata.regionIndex[i]] += mydata.fixedCost[i]*x[i];
	}

	cout << "total_open_facility: " << total_open_facility << endl;

	for (int j = 0; j < mydata.Nregions; j++)
		cout << "region[" << j << "]= " << num_facility_in_region[j] << "\t" << inv_facility_in_region[j] << endl;

	/* this might be useful for the equality constraint
	vector<double> s(mydata.Ncust);
	CPXgetx(mydata.envOrigProblem, mydata.origProblem, &s.front(), mydata.NCol, mydata.NCol + mydata.Ncust - 1);
	for (int i = 0; i<mydata.Ncust; i++)
		cout << "s[" << i << "] " << s[i] << endl;
	*/

	if (mydata.origProblem != NULL)
		CPXfreeprob(mydata.envOrigProblem, &mydata.origProblem);

	if (mydata.envOrigProblem != NULL)
		CPXcloseCPLEX(&mydata.envOrigProblem);

	if (mydata.apprxProblem != NULL)
		CPXfreeprob(mydata.envApprxProblem, &mydata.apprxProblem);

	if (mydata.envApprxProblem != NULL)
		CPXcloseCPLEX(&mydata.envApprxProblem);

	return (0);


} // END main 


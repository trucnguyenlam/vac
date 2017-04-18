#include "ARBACAbstract.h"

namespace Abstract {

	// Declare variables for Integer program
	static void
	declare_variables(FILE *out)
	{
		int i;

		fprintf(out, "//-------- DECLARE VARIBLES ----------//\n");
		fprintf(out, "var");

		// Declare variables for users
		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\tb_%s : int ,\n", role_array[i]);
		}

		// Declare variables for administrators
		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\td_%s : int ,\n", role_array[i]);
		}

		// Declare integer variables for each Venn region (P,N)
		for (i = 0; i < venn_region_array_size - 1; i++)
		{
			fprintf(out, "\t%s : int ,\n", venn_region_array[i]);
		}
		fprintf(out, "\t%s : int ;\n", venn_region_array[i]);
	}

	static void
	initialize_variables(FILE *out)
	{
		int i, num;

		fprintf(out, "\t//-------------- Init VARS ------------------------//\n");

		// User
		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\tb_%s = 0;\n", role_array[i]);
		}
		// Administrator
		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\td_%s = 0;\n", role_array[i]);
		}

		for (i = 0; i < venn_region_array_size; i++)
		{
			fprintf(out, "\t%s = 0;\n", venn_region_array[i]);
		}

		fprintf(out, "\t// Initialize track variables in the system\n");
		for (i = 0; i < Track_size; i++)
		{
			num = get_number_of_venn_region(Track[i]);
			if (num != 0)
			{
				fprintf(out, "\t%s = %s + %d;\n", venn_region_array[i], venn_region_array[i], num);
			}
		}
	}

	// Assign value for variables non-deterministically
	static void
	non_deter_assign_variables(FILE *out)
	{
		int i;

		fprintf(out, "\t\t//----- Non-deterministic assignment ------//\n");
		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\t\tb_%s = random; assume b_%s >= 0 and b_%s <= 1;\n", role_array[i], role_array[i], role_array[i]);
		}
		fprintf(out, "\n");

		for (i = 0; i < role_array_size; i++)
		{
			fprintf(out, "\t\td_%s = random; assume d_%s >= 0 and d_%s <= 1;\n", role_array[i], role_array[i], role_array[i]);
		}
		fprintf(out, "\n");
	}

	static int
	equal_Venn_regions(venn_region v1, venn_region v2)
	{
		if (equal_set(v1.P, v2.P) && equal_set(v1.N, v2.N))
		{
			return 1;
		}
		else
		{
			return 0;
		}
	}

	// Print psi(b) function for the users as corresponding in can assign rule
	static void
	psi_user_ca(FILE *out, int ca_rule)
	{
		int i;

		venn_region v; /* Temporary venn_region */

		v.P.array = 0;
		v.P.array_size = 0;
		v.N.array = 0;
		v.N.array_size = 0;

		v.P = build_set(ca_array[ca_rule].positive_role_array, ca_array[ca_rule].positive_role_array_size);
		v.N = build_set(ca_array[ca_rule].negative_role_array, ca_array[ca_rule].negative_role_array_size);

		int index = -1;
		for (i = 0; i < Track_size; i++)
		{
			if (equal_Venn_regions(Track[i], v))
			{
				index = i;
				break;
			}
		}

		free(v.P.array);
		v.P.array = 0;
		free(v.N.array);
		v.N.array = 0;

		if (index == -1)
		{
			fprintf(stderr, "error: there is something wrong when translate into INTERPROC\n");
			abort();
		}
		else
		{
			fprintf(out, " and %s>0", venn_region_array[index]);
		}

	}

	// Print psi(d) function for the administrator as corresponding in can assign rule
	static void
	psi_admin_ca(FILE *out, int ca_rule)
	{
		fprintf(out, " and n_%s>0", role_array[ca_array[ca_rule].admin_role_index]);
	}

	// Implement coh(P,N)
	static void
	coherent_Venn_region(FILE *out, set P, set N)
	{
		int i;

		for (i = 0; i < P.array_size; i++)
		{
			if (i == 0)
			{
				fprintf(out, "b_%s==1", role_array[P.array[i]]);
			}
			else
			{
				fprintf(out, " and b_%s==1", role_array[P.array[i]]);
			}
		}

		if (P.array_size != 0 && N.array_size != 0)
		{
			fprintf(out, " and ");
		}

		for (i = 0; i < N.array_size; i++)
		{
			if (i == 0)
			{
				fprintf(out, "b_%s==0", role_array[N.array[i]]);
			}
			else
			{
				fprintf(out, " and b_%s==0", role_array[N.array[i]]);
			}
		}

		// If nothing in P nor N print true
		if (P.array_size == 0 && N.array_size == 0)
		{
			fprintf(out, "true");
		}
	}

	// Implementation of coh((Pos, Neg),b))
	static void
	coh_Pos_Neg(FILE *out, int ca_rule)
	{
		set P, N;

		P = build_set(ca_array[ca_rule].positive_role_array, ca_array[ca_rule].positive_role_array_size);
		N = build_set(ca_array[ca_rule].negative_role_array, ca_array[ca_rule].negative_role_array_size);

		fprintf(out, " and ");
		coherent_Venn_region(out, P, N);

		free(P.array);
		free(N.array);
	}

	// Implementation of phi_ca(b) - The transition abstraction
	static void
	phi_ca(FILE *out, int ca_rule)
	{
		int i, flag = 0;
		set P, tmp;

		for (i = 0; i < Track_size; i++)
		{
			// For each Venn region that target role belong to Positive set
			if (belong_to(Track[i].P.array, Track[i].P.array_size, ca_array[ca_rule].target_role_index))
			{
				tmp = duplicate_set(Track[i].P);
				P = remove_element(tmp, ca_array[ca_rule].target_role_index);

				// Case of something appear in the coherent
				fprintf(out, "\t\t\tif(");
				coherent_Venn_region(out, P, Track[i].N);
				fprintf(out, ") then\n");

				fprintf(out, "\t\t\t\t%s = %s+1;\n", venn_region_array[i], venn_region_array[i]);

				fprintf(out, "\t\t\tendif;\n");

				free(P.array);

				flag = 1;
			}

			// The precondition is NEW
			if (ca_array[ca_rule].type != 2)
			{
				// For each Venn region that target role belong to Positive set
				if (belong_to(Track[i].N.array, Track[i].N.array_size, ca_array[ca_rule].target_role_index))
				{

					fprintf(out, "\t\t\tif(");
					coherent_Venn_region(out, Track[i].P, Track[i].N);
					fprintf(out, " and %s>0", venn_region_array[i]);
					fprintf(out, ") then\n");

					fprintf(out, "\t\t\t\t%s = %s-1;\n", venn_region_array[i], venn_region_array[i]);

					fprintf(out, "\t\t\tendif;\n");
					flag = 1;
				}
			}
		}

		if (!flag)
		{
			fprintf(out, "\t\t\tassume true;\n");
		}
	}

	// Transform a can assign rule
	static void
	transform_ca_rule(FILE *out, int ca_rule)
	{
		// Print comment of CA rules
		print_ca_comment(out, ca_rule);

		// Print d_admin here
		fprintf(out, "\t\tif(brandom and d_%s==1", role_array[ca_array[ca_rule].admin_role_index]);

		// Print psi(d)
		psi_admin_ca(out, ca_rule);

		// Print coh((Pos, Neg),b)
		if (ca_array[ca_rule].type == 0) // For normal rule
		{
			coh_Pos_Neg(out, ca_rule);
			psi_user_ca(out, ca_rule);
		}

		// End condition
		fprintf(out, ") then\n");

		// Print phi_ca
		phi_ca(out, ca_rule);

		// End
		fprintf(out, "\t\tendif;\n\n");
	}

	// Transform array of can assign rules
	static void
	transform_ca_array(FILE *out)
	{
		int i;

		for (i = 0; i < ca_array_size; i++)
		{
			transform_ca_rule(out, i);
		}
	}

	// Implement of psi(b) for a can revoke rule
	static void
	psi_user_cr(FILE *out, int cr_rule)
	{
		fprintf(out, " and b_%s==1", role_array[cr_array[cr_rule].target_role_index]);
	}

	// Implement of psi(d) for a can revoke rule
	static void
	psi_admin_cr(FILE *out, int cr_rule)
	{
		fprintf(out, " and n_%s>0", role_array[cr_array[cr_rule].admin_role_index]);
	}

	// Simulation of can revoke rule phi_cr
	static void
	phi_cr(FILE *out, int cr_rule)
	{
		int i, flag = 0;
		set N, tmp;

		for (i = 0; i < Track_size; i++)
		{
			// For each Venn region that target role belong to Positive set
			if (belong_to(Track[i].P.array, Track[i].P.array_size, cr_array[cr_rule].target_role_index))
			{
				// Case of something appear in the coherent
				fprintf(out, "\t\t\tif(");
				coherent_Venn_region(out, Track[i].P, Track[i].N);
				fprintf(out, " and %s>0", venn_region_array[i]);
				fprintf(out, ") then\n");

				fprintf(out, "\t\t\t\t%s = %s-1;\n", venn_region_array[i], venn_region_array[i]);

				fprintf(out, "\t\t\tendif;\n");
				flag = 1;
			}

			// For each Venn region that target role belong to Positive set
			if (belong_to(Track[i].N.array, Track[i].N.array_size, cr_array[cr_rule].target_role_index))
			{
				tmp = duplicate_set(Track[i].N);
				N = remove_element(tmp, cr_array[cr_rule].target_role_index);

				fprintf(out, "\t\t\tif(");
				coherent_Venn_region(out, Track[i].P, N);
				fprintf(out, ") then\n");

				fprintf(out, "\t\t\t\t%s = %s+1;\n", venn_region_array[i], venn_region_array[i]);

				fprintf(out, "\t\t\tendif;\n");

				free(N.array);
				flag = 1;
			}
		}

		if (!flag) // Do nothing
		{
			fprintf(out, "\t\t\tassume true;\n");
		}
	}

	// Transform a can revoke rule
	static void
	transform_cr_rule(FILE *out, int cr_rule)
	{
		// Print comment of CR rules;
		print_cr_comment(out, cr_rule);

		fprintf(out, "\t\tif(brandom and d_%s==1", role_array[cr_array[cr_rule].admin_role_index]);

		// Print psi(d)
		psi_admin_cr(out, cr_rule);

		psi_user_cr(out, cr_rule);

		fprintf(out, ") then\n");

		// Print phi_cr
		phi_cr(out, cr_rule);

		fprintf(out, "\t\tendif;\n\n");
	}

	// Transform array of can revoke rules
	static void
	transform_cr_array(FILE *out)
	{
		int i;
		for (i = 0; i < cr_array_size; i++)
		{
			transform_cr_rule(out, i);
		}
	}

	static void
	simulation(FILE *out)
	{
		// While loop
		fprintf(out, "\n\twhile ( true )  do \n\n");

		// Non deterministically allocate variables
		non_deter_assign_variables(out);

		fprintf(out, "\t\t//-------------- Simulation -------------------//\n");
		// Transform can assign rules
		transform_ca_array(out);

		// Transform can revoke rules
		transform_cr_array(out);

		// ERROR defined
		fprintf(out, "\t\t//------------ ERROR Query ---------------//\n");
		fprintf(out, "\t\tif (%s>0) then\n\t\t\tskip;\n\t\tendif;\n", query);
		fprintf(out, "\tdone;  //End while loop\n");
	}

	// Transform function
	void
	transform_2_INTERPROC_OverApr(char *fileName, FILE *outputFile)
	{
		/*
		FILE *out;
		char *newfile = 0;

		newfile = malloc(strlen(fileName) + strlen("_OverApx_INTERPROC.cpp") + 2);
		sprintf(newfile, "%s_OverApx_INTERPROC.cpp", fileName);
		out = fopen(newfile, "w");
		*/

		read_ARBAC(fileName);

		reduction_finiteARBAC();

		// Build the Track
		build_Track();
		build_Venn_region_string_array();
		build_user_configurations();

		// Declare variable
		declare_variables(outputFile);

		// Begin main program
		fprintf(outputFile, "\n//-------------- BEGIN Program --------------------//\n");
		fprintf(outputFile, "begin\n");

		// Init data
		initialize_variables(outputFile);

		// Simulation
		simulation(outputFile);

		fprintf(outputFile, "end  //End main\n");

		// End
		/*
		fclose(outputFile);
		free(newfile);*/
		free_data();
		free_abstract_temp_data();
	}

}

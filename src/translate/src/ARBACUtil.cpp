#include <stdlib.h>
#include "ARBACUtil.h"

/**********************************************************************
 * Function belong_to
 * Check if some belong to an array
 * @param array : array to check
 * @param array_size : size
 * @param index : the index to check
 * @return 1 if satisfy 0 otherwise
 **********************************************************************/
int
belong_to(int * array, int array_size, int index)
{
	int i;
	if (array_size == 0)
	{
		return 0;
	}
	for (i = 0; i < array_size; i++)
	{
		if (index == array[i])
		{
			return 1;
		}
	}
	return 0;
}

/**********************************************************************
 * Function belong_to
 * Check if some belong to an array
 * @param array : array to check
 * @param array_size : size
 * @param index : the index to check
 * @return 1 if satisfy 0 otherwise
 **********************************************************************/
int
index_of(int num, int * array, int array_size)
{
	int i;

	if (array_size == 0)
	{
		return -1;
	}
	for (i = 0; i < array_size; i++)
	{
		if (num == array[i])
		{
			return i;
		}
	}
	return -1;
}

/**********************************************************************
 * Function subset_of
 * Check if some set subset of other set
 * @param set1
 * @param set2
 * @return 1 if satisfy 0 otherwise
 **********************************************************************/
int
subset_of(set set1, set set2)
{
	int i;
	if (set1.array_size == 0)
	{
		return 1;
	}
	for (i = 0; i < set1.array_size; i++)
	{
		if (!belong_to(set2.array, set2.array_size, set1.array[i]))
		{
			return 0;
		}
	}
	return 1;
}

/**********************************************************************
 * Function equal_set
 * Check if two set are equal
 * @param set1
 * @param set2
 * @return 1 if satisfy 0 otherwise
 **********************************************************************/
int
equal_set(set set1, set set2)
{
	int i;

	if (set1.array_size != set2.array_size)
	{
		return 0;
	}

	for (i = 0; i < set1.array_size; i++)
	{
		if (!belong_to(set2.array, set2.array_size, set1.array[i]))
		{
			return 0;
		}
	}
	return 1;
}

/**********************************************************************
 * Function add_last_element
 * Append an element to a set
 * @param s : set to be added
 * @param element
 * @return the result set
 **********************************************************************/
set
add_last_element(set s, int element)
{
	s.array_size++;
	s.array = (int *) realloc(s.array, s.array_size * sizeof(int));
	s.array[s.array_size - 1] = element;
	return s;
}

/**********************************************************************
 * Function add_element
 * To add an element to a set
 * @param s : set to be added
 * @param element
 * @return the result set
 **********************************************************************/
set
add_element(set s, int element)
{
	if (!belong_to(s.array, s.array_size, element))
	{
		s = add_last_element(s, element);
	}
	return s;
}

/**********************************************************************
 * Function remove_element
 * Remove an element to a set
 * @param s : set to be added
 * @param element
 * @return the result set
 **********************************************************************/
set
remove_element(set s, int element)
{
	set result, remove;

	remove.array_size = 1;
	remove.array = (int *) malloc(sizeof(int));
	remove.array[0] = element;

	result = different_set(s, remove);
	return result;
}

/**********************************************************************
 * Function union_set
 * Union two sets
 * @param set1
 * @param set2
 * @return union set
 **********************************************************************/
set
union_set(set set1, set set2)
{
	set result;
	int i;

	if (set1.array_size == 0)
	{
		return set2;
	}
	if (set2.array_size == 0)
	{
		return set1;
	}

	result.array_size = set1.array_size;
	result.array = (int *) malloc(result.array_size * sizeof(int));

	for (i = 0; i < set1.array_size; i++)
	{
		result.array[i] = set1.array[i];
	}

	for (i = 0; i < set2.array_size; i++)
	{
		if (!belong_to(set1.array, set1.array_size, set2.array[i]))
		{
			result.array_size++;
			result.array = (int *) realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set2.array[i];
		}
	}

	// free(set1.array);
	// set1.array = 0;
	// free(set2.array);
	// set2.array = 0;

	return result;
}

/**********************************************************************
 * Function intersect_set
 * Intersect two sets
 * @param set1
 * @param set2
 * @return intersection set
 **********************************************************************/
set
intersect_set(set set1, set set2)
{
	set result;
	int i;

	result.array = 0;
	result.array_size = 0;

	if (set1.array_size == 0 || set2.array_size == 0)
	{
		return result;
	}

	for (i = 0; i < set2.array_size; i++)
	{
		if (belong_to(set1.array, set1.array_size, set2.array[i]))
		{
			result.array_size++;
			result.array = (int *) realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set2.array[i];
		}
	}

	// free(set1.array);
	// set1.array = 0;
	// free(set2.array);
	// set2.array = 0;

	return result;
}

/**********************************************************************
 * Function different_set
 * Different set1 from set2
 * @param set1
 * @param set2
 * @return the different set
 **********************************************************************/
set
different_set(set set1, set set2)
{
	set result;
	int i;

	result.array = 0;
	result.array_size = 0;

	if (set1.array_size == 0)
	{
		return result;
	}

	if (set2.array_size == 0)
	{
		return set1;
	}

	for (i = 0; i < set1.array_size; i++)
	{
		if (!belong_to(set2.array, set2.array_size, set1.array[i]))
		{
			result.array_size++;
			result.array = (int *) realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set1.array[i];
		}
	}

	// free(set1.array);
	// set1.array = 0;
	// free(set2.array);
	// set2.array = 0;
	
	return result;
}

/**********************************************************************
 * Function duplicate_set
 * @param someset
 * @return the duplicate set
 **********************************************************************/
set
duplicate_set(set someset)
{
	set result;
	int i;

	result.array = 0;
	result.array_size = 0;

	if (someset.array_size == 0)
	{
		return result;
	}

	result.array_size = someset.array_size;
	result.array = (int *) malloc(result.array_size * sizeof(int));

	for (i = 0; i < someset.array_size; i++)
	{
		result.array[i] = someset.array[i];
	}

	return result;
}

/**********************************************************************
 * Function build_set
 * @param array : array to build
 * @param array_size : size of that array
 * @return the built set
 **********************************************************************/
set
build_set(int * array, int array_size)
{
	set result;
	int i;

	result.array = 0;
	result.array_size = array_size;

	if (array_size == 0)
	{
		return result;
	}

	result.array = (int *) malloc(result.array_size * sizeof(int));

	for (i = 0; i < array_size; i++)
	{
		result.array[i] = array[i];
	}
	return result;
}

#include <stdlib.h>
#include "ARBACUtil.h"

int
belong_to(int *array, int array_size, int index)
{
	int i;
	if (array_size == 0)
	{
		return -1;
	}
	for (i = 0; i < array_size; i++)
	{
		if (array[i] != -13 && index == array[i])
		{
			return i;
		}
	}
	return -1;
}

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
		if (belong_to(set2.array, set2.array_size, set1.array[i]) == -1)
		{
			return 0;
		}
	}
	return 1;
}

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
		if (belong_to(set2.array, set2.array_size, set1.array[i]) == -1)
		{
			return 0;
		}
	}
	return 1;
}

set
add_last_element(set s, int element)
{
	s.array_size++;
	s.array = realloc(s.array, s.array_size * sizeof(int));
	s.array[s.array_size - 1] = element;
	return s;
}

set
add_element(set s, int element)
{
	if (belong_to(s.array, s.array_size, element) == -1)
	{
		s = add_last_element(s, element);
	}
	return s;
}

set
remove_element(set s, int element)
{
	set result, remove;

	remove.array_size = 1;
	remove.array = malloc(sizeof(int));
	remove.array[0] = element;

	result = different_set(s, remove);
	return result;
}

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
	result.array = malloc(result.array_size * sizeof(int));

	for (i = 0; i < set1.array_size; i++)
	{
		result.array[i] = set1.array[i];
	}

	for (i = 0; i < set2.array_size; i++)
	{
		if (belong_to(set1.array, set1.array_size, set2.array[i]) == -1)
		{
			result.array_size++;
			result.array = realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set2.array[i];
		}
	}

	// Free two sets (memory leak prevention)
	free(set1.array);
	set1.array = 0;
	free(set2.array);
	set2.array = 0;

	return result;
}

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
		if (belong_to(set1.array, set1.array_size, set2.array[i]) != -1)
		{
			result.array_size++;
			result.array = realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set2.array[i];
		}
	}

	free(set1.array);
	set1.array = 0;
	free(set2.array);
	set2.array = 0;

	return result;
}

set
different_set(set set1, set set2)
{
	int i;
	set result;

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
		if (belong_to(set2.array, set2.array_size, set1.array[i]) == -1)
		{
			result.array_size++;
			result.array = realloc(result.array, result.array_size * sizeof(int));
			result.array[result.array_size - 1] = set1.array[i];
		}
	}

	// Free two sets (memory leak prevention)

	free(set1.array);
	set1.array = 0;
	free(set2.array);
	set2.array = 0;

	return result;
}

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
	result.array = malloc(result.array_size * sizeof(int));

	for (i = 0; i < someset.array_size; i++)
	{
		result.array[i] = someset.array[i];
	}

	return result;
}

set
build_set(int *array, int array_size)
{
	set result;
	int i;

	result.array = 0;
	result.array_size = 0;

	if (array_size == 0)
	{
		return result;
	}

	for (i = 0; i < array_size; i++)
	{
		if (array[i] != -13)
		{
			result = add_last_element(result, array[i]);
		}
	}
	return result;
}

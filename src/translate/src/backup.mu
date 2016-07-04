// ####### #     # ######  #######      #
//    #     #   #  #     # #           ##
//    #      # #   #     # #          # #
//    #       #    ######  #####        #
//    #       #    #       #            #
//    #       #    #       #            #
//    #       #    #       #######    #####

// //*************** Round 0
//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               & (
//                   ( CanAssign( t_CL, t_G.h0, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h0, s_G.h0 )
//                   )
//                   | CanRevoke( t_CL, t_G.h0, s_CL, s_G.h0 )
//                 )
//            )
//       )
//     )

// //*************** Round 1
//   |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists16 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               & (
//                   ( CanAssign( t_CL, t_G.h1, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h1, s_G.h1 )
//                   )
//                   | CanRevoke( t_CL, t_G.h1, s_CL, s_G.h1 )
//                 )
//            )
//       )
//     )

// //*************** Round 2
//   |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists17 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               & (
//                   ( CanAssign( t_CL, t_G.h2, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h2, s_G.h2 )
//                   )
//                   | CanRevoke( t_CL, t_G.h2, s_CL, s_G.h2 )
//                 )
//            )
//       )
//     )

// //*************** Round 3
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists18 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               & (
//                   ( CanAssign( t_CL, t_G.h3, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h3, s_G.h3 )
//                   )
//                   | CanRevoke( t_CL, t_G.h3, s_CL, s_G.h3 )
//                 )
//            )
//       )
//     )


// ####### #     # ######  #######     #####
//    #     #   #  #     # #          #     #
//    #      # #   #     # #                #
//    #       #    ######  #####       #####
//    #       #    #       #          #
//    #       #    #       #          #
//    #       #    #       #######    #######

// //*************** Round 0
//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h0, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h0, s_G.h0 )
//                   )
//                   | CanAssign( t_CL, t_G.h0, s_CL, s_G.h0 )
//                 )
//            )
//       )
//     )

// //*************** Round 1
//   |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists16 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h1, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h1, s_G.h1 )
//                   )
//                   | CanAssign( t_CL, t_G.h1, s_CL, s_G.h1 )
//                 )
//            )
//       )
//     )

// //*************** Round 2
//   |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists17 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h2, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h2, s_G.h2 )
//                   )
//                   | CanAssign( t_CL, t_G.h2, s_CL, s_G.h2 )
//                 )
//            )
//       )
//     )

// //*************** Round 3
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists18 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h3, s_CL )
//                     & UpdateGlobal( s_CL, t_G.h3, s_G.h3 )
//                   )
//                   | CanAssign( t_CL, t_G.h3, s_CL, s_G.h3 )
//                 )
//            )
//       )
//     )


// ####### #     # ######  #######     #####
//    #     #   #  #     # #          #     #
//    #      # #   #     # #                #
//    #       #    ######  #####       #####
//    #       #    #       #                #
//    #       #    #       #          #     #
//    #       #    #       #######     #####

// //*************** Round 0
//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h0, s_CL )
//                   | CanAssign( t_CL, t_G.h0, s_CL )
//                   )
//                   & UpdateGlobal( s_CL, t_G.h0, s_G.h0 )
//                 )
//            )
//       )
//     )

// //*************** Round 1
//   |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists16 */              // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h1, s_CL )
//                   | CanAssign( t_CL, t_G.h1, s_CL)
//                   )
//                   & UpdateGlobal( s_CL, t_G.h1, s_G.h1 )
//                 )
//            )
//       )
//     )

// //*************** Round 2
//   |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists17 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h2, s_CL )
//                   | CanAssign( t_CL, t_G.h2, s_CL )
//                   )
//                   & UpdateGlobal( s_CL, t_G.h2, s_G.h2 )
//                 )
//            )
//       )
//     )

// //*************** Round 3
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists18 */            // There exists an internal state that
//            Roles   t_CL,
//            Globals t_G.
//            (    Sequ_Reach( s_block, s_r, s_ID, t_CL, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               & (
//                   ( CanRevoke( t_CL, t_G.h3, s_CL )
//                   | CanAssign( t_CL, t_G.h3, s_CL )
//                   )
//                   & UpdateGlobal( s_CL, t_G.h3, s_G.h3 )
//                 )
//            )
//       )
//     )
// ####### #     # ######  #######    #######
//    #     #   #  #     # #          #
//    #      # #   #     # #          #
//    #       #    ######  #####      ######
//    #       #    #       #                #
//    #       #    #       #          #     #
//    #       #    #       #######     #####
//
// //*************** Round 0
//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists15 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               ) & (
//                     CanAssign( t_G.L, t_G.h0, s_G.L, s_G.h0 )
//               )
//            )
//       )
//     )

//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists16 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               )
//             & ( CanRevoke( t_G.L, t_G.h0, s_G.L, s_G.h0 )
//               )
//            )
//       )
//     )

//   |  (
//         (   s_r=0      // Round 0
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists17 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_0( s_G, t_G )
//               )
//             & ( UpdateGlobal( t_G.h0, s_G.L, s_G.h0 )
//                & s_G.L = t_G.L
//               )
//            )
//       )
//     )

// //*************** Round 1
//   |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists18 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               ) & (
//                     CanAssign( t_G.L, t_G.h1, s_G.L, s_G.h1 )
//               )
//            )
//       )
//     )
//  |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists19 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               )
//             & ( CanRevoke( t_G.L, t_G.h1, s_G.L, s_G.h1 )
//               )
//            )
//       )
//     )
//  |  (
//         (   s_r=1      // Round 1
//           & (s_block=thread)
//         )
//       & (exists      /* Sequ_Reach::@Exists20 */              // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_1( s_G, t_G )
//               )
//             & ( UpdateGlobal( t_G.h1, s_G.L, s_G.h1 )
//                & s_G.L = t_G.L
//               )
//            )
//       )
//     )

// //*************** Round 2
//   |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists21 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               ) & (
//                     CanAssign( t_G.L, t_G.h2, s_G.L, s_G.h2 )
//               )
//            )
//       )
//     )
//  |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists22 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               )
//             & ( CanRevoke( t_G.L, t_G.h2, s_G.L, s_G.h2 )
//               )
//            )
//       )
//     )
//  |  (
//         (   s_r=2      // Round 2
//           & (s_block=thread)
//         )
//       & (exists         /* Sequ_Reach::@Exists23 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_2( s_G, t_G )
//               )
//             & ( UpdateGlobal( t_G.h2, s_G.L, s_G.h2 )
//                & s_G.L = t_G.L
//               )
//            )
//       )
//     )

// //*************** Round 3
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists24 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               ) & (
//                     CanAssign( t_G.L, t_G.h3, s_G.L, s_G.h3 )
//               )
//            )
//       )
//     )
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists25 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               )
//             & ( CanRevoke( t_G.L, t_G.h3, s_G.L, s_G.h3 )
//               )
//            )
//       )
//     )
//   |  (
//         (   s_r=3     // Round 3
//           & (s_block=thread)
//         )
//       & (exists        /* Sequ_Reach::@Exists26 */            // There exists an internal state that
//            Globals t_G.
//            (  (  Sequ_Reach( s_block, s_r, s_ID, t_G )
//               & copy_g_and_h_3( s_G, t_G )
//               )
//             & ( UpdateGlobal( t_G.h3, s_G.L, s_G.h3 )
//                & s_G.L = t_G.L
//               )
//            )
//       )
//     )


// ######## ##    ## ########  ########       ##
//    ##     ##  ##  ##     ## ##           ####
//    ##      ####   ##     ## ##             ##
//    ##       ##    ########  ######         ##
//    ##       ##    ##        ##             ##
//    ##       ##    ##        ##             ##
//    ##       ##    ##        ########     ######


#ifdef TRANSLATION_TYPE1
static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "(cG.%s=true", role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=true", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") & /* Applying this rule */\n");
    // Applying this rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
    {
        fprintf(outputFile, " (dL.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, " (dL.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    }
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    // for (i = 0; i < admin_role_array_index_size; i++)
    // {
    //     if (admin_role_array_index[i] != ca_array[ca_rule].target_role_index)
    //     {
    //         fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    //     }
    // }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanAssign(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL\n");
/*
  cL  <  cG,
  cL  ~+  dL
 */

    fprintf(outputFile, "(false \n");
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, "\t/ *Rule with NEW in the precondition are already involved in initialization */\n");
        }
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanAssign;\n\n");
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "| ( /* condition */\n");
    // Admin role must be available
    if (cr_array[cr_rule].admin_role_index < 0)
    {
        fprintf(outputFile, " (true");
    }
    else
    {
        fprintf(outputFile, " (cG.%s=true", role_array[cr_array[cr_rule].admin_role_index]);
    }
    // The user must be in that target role
    fprintf(outputFile, " & cL.%s=true", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    {
        fprintf(outputFile, " (dL.%s=false & dG.%s=false)\n", role_array[cr_array[cr_rule].target_role_index], role_array[cr_array[cr_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "(dL.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanRevoke(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL,\n");
    fprintf(outputFile, "  dL  ~+  dG\n");
    /*
  cL  <  cG,
  cL  ~+  dL,
  dL  <  dG,
  cG  ~+  dG
    */

    fprintf(outputFile, "(false \n");

    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanRevoke;\n\n");

}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
    fprintf(outputFile, "bool UpdateGlobal(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");

    fprintf(outputFile, "(true \n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size UpdateGlobal;\n\n");
}

#endif

// ######## ##    ## ########  ########     #######
//    ##     ##  ##  ##     ## ##          ##     ##
//    ##      ####   ##     ## ##                 ##
//    ##       ##    ########  ######       #######
//    ##       ##    ##        ##          ##
//    ##       ##    ##        ##          ##
//    ##       ##    ##        ########    #########


#ifdef TRANSLATION_TYPE2
static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "(cG.%s=true", role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=true", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") & /* Applying this rule */\n");
    // Applying this rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
    {
        fprintf(outputFile, " (dL.%s=true) & (dG.%s=true)\n", role_array[ca_array[ca_rule].target_role_index], role_array[ca_array[ca_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, " (dL.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    }
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanAssign(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL,\n");
    fprintf(outputFile, "  dL  ~+  dG\n");
    fprintf(outputFile, "(false \n");
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, "\t/ *Rule with NEW in the precondition are already involved in initialization */\n");
        }
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanAssign;\n\n");
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "| ( /* condition */\n");
    // Admin role must be available
    if (cr_array[cr_rule].admin_role_index < 0)
    {
        fprintf(outputFile, " (true");
    }
    else
    {
        fprintf(outputFile, " (cG.%s=true", role_array[cr_array[cr_rule].admin_role_index]);
    }
    // The user must be in that target role
    fprintf(outputFile, " & cL.%s=true", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    fprintf(outputFile, "(dL.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    // for (i = 0; i < admin_role_array_index_size; i++)
    // {
    //     if (admin_role_array_index[i] != cr_array[cr_rule].target_role_index)
    //     {
    //         fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    //     }
    // }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanRevoke(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL\n");

    fprintf(outputFile, "(false \n");

    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanRevoke;\n\n");

}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
    fprintf(outputFile, "bool UpdateGlobal(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");

    fprintf(outputFile, "(true \n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size UpdateGlobal;\n\n");
}

#endif


// ######## ##    ## ########  ########     #######
//    ##     ##  ##  ##     ## ##          ##     ##
//    ##      ####   ##     ## ##                 ##
//    ##       ##    ########  ######       #######
//    ##       ##    ##        ##                 ##
//    ##       ##    ##        ##          ##     ##
//    ##       ##    ##        ########     #######


#ifdef TRANSLATION_TYPE3
static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "(cG.%s=true", role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=true", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") & /* Applying this rule */\n");
    // Applying this rule
    fprintf(outputFile, " (dL.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanAssign(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL\n");
    fprintf(outputFile, "(false \n");
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, "\t/ *Rule with NEW in the precondition are already involved in initialization */\n");
        }
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanAssign;\n\n");
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "| ( /* condition */\n");
    // Admin role must be available
    if (cr_array[cr_rule].admin_role_index < 0)
    {
        fprintf(outputFile, " (true");
    }
    else
    {
        fprintf(outputFile, " (cG.%s=true", role_array[cr_array[cr_rule].admin_role_index]);
    }
    // The user must be in that target role
    fprintf(outputFile, " & cL.%s=true", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    {
        fprintf(outputFile, "(dL.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "(dL.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanRevoke(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dL\n");

    fprintf(outputFile, "(false \n");

    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanRevoke;\n\n");

}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
    fprintf(outputFile, "bool UpdateGlobal(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+  cG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");
/*
  cL  <   cG,
  cG  ~+  dG
 */
    fprintf(outputFile, "(true \n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=cL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size UpdateGlobal;\n\n");
}

#endif

// ######## ##    ## ########  ########    ########
//    ##     ##  ##  ##     ## ##          ##
//    ##      ####   ##     ## ##          ##
//    ##       ##    ########  ######      #######
//    ##       ##    ##        ##                ##
//    ##       ##    ##        ##          ##    ##
//    ##       ##    ##        ########     ######

#ifdef TRANSLATION_TYPE5
static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "(cG.%s=true", role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=true", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & cL.%s=false", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") & /* Applying this rule */\n");
    // Applying this rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
    {
        fprintf(outputFile, " (dL.%s=true) & (dG.%s=true)\n", role_array[ca_array[ca_rule].target_role_index], role_array[ca_array[ca_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, " (dL.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    }

    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        }
        // else
        // {
        //     fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        // }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanAssign(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+   cG,\n");
    fprintf(outputFile, "  cL  ~+  dL,\n");
    fprintf(outputFile, "  dL  ~+   dG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");
    fprintf(outputFile, "(false \n");
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, "\t/ *Rule with NEW in the precondition are already involved in initialization */\n");
        }
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanAssign;\n\n");
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "| ( /* condition */\n");
    // Admin role must be available
    if (cr_array[cr_rule].admin_role_index < 0)
    {
        fprintf(outputFile, " (true");
    }
    else
    {
        fprintf(outputFile, " (cG.%s=true", role_array[cr_array[cr_rule].admin_role_index]);
    }
    // The user must be in that target role
    fprintf(outputFile, " & cL.%s=true", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    {
        fprintf(outputFile, "(dL.%s=false) & (dG.%s=false)\n", role_array[cr_array[cr_rule].target_role_index], role_array[cr_array[cr_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "(dL.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dL.%s=cL.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        }
        // else
        // {
        //     fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        // }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    fprintf(outputFile, "bool CanRevoke(\n");
    fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  cL  ~+   cG,\n");
    fprintf(outputFile, "  cL  ~+  dL,\n");
    fprintf(outputFile, "  dL  ~+   dG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");
    fprintf(outputFile, "(false \n");

    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size CanRevoke;\n\n");

}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i, j;
    fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
    fprintf(outputFile, "bool UpdateGlobal(\n");
    // fprintf(outputFile, "   Roles cL,\n");
    fprintf(outputFile, "   Roles cG,\n");
    fprintf(outputFile, "   Roles dL,\n");
    fprintf(outputFile, "   Roles dG\n");
    fprintf(outputFile, ")\n");
    // fprintf(outputFile, "  cL  ~+  cG,\n");
    // fprintf(outputFile, "  cL  ~+  dL,\n");
    fprintf(outputFile, "  dL  ~+  dG,\n");
    fprintf(outputFile, "  cG  ~+  dG\n");
    fprintf(outputFile, "(true \n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        fprintf(outputFile, "& ((dG.%s=cG.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        for (j = 0; j < cr_array_size; j++)
        {
            if (admin_role_array_index[i] == cr_array[j].target_role_index)
            {
                fprintf(outputFile, "|(dG.%s=dL.%s)", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
                break;
            }
        }
        fprintf(outputFile, ")\n");
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size UpdateGlobal;\n\n");
}

#endif



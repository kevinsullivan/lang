import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr

namespace peirce_output
noncomputable theory

def wt_fr : time_frame_expr := |time_std_frame|
def wt : time_space_expr wt_fr := |time_std_space|

def ww_fr : geom3d_frame_expr := |geom3d_std_frame|
def ww : geom3d_space_expr ww_fr := |geom3d_std_space|

def bl_fr : geom3d_frame_expr := 
 let origin := |mk_position3d ww.value 1.000000 1.000000 1.000000| in
 let basis0 := |mk_displacement3d ww.value 1.000000 1.000000 1.000000| in
 let basis1 := |mk_displacement3d ww.value 1.000000 1.000000 1.000000| in
 let basis2 := |mk_displacement3d ww.value 1.000000 1.000000 1.000000| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def bl : geom3d_space_expr bl_fr := mk_geom3d_space_expr bl_fr

def wtobl : geom3d_transform_series_expr wt ww bl := |[
		⟨(mk_time wt.value 0.000000),(ww.value.mk_geom3d_transform_to bl.value)⟩]|

def target_pose_in_world 
	: (constrained (timestamped_pose3d_expr wt ww) (time range |1| to |100|))--(timestamped_pose3d_expr.range_constraint 1 100))
		:= 
		{
			val := |(|mk_time _ 10|),(|mk_pose3d ww.value 
			(mk_orientation3d ww.value 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000)
			(mk_position3d ww.value 1.000000 1.000000 1.000000)|)|,
			holds := begin 
				unfold has_time_range_constraint.to_range_constraint,
				let h0 : (|(|mk_time wt.value 10|),
					(|mk_pose3d ww.value (mk_orientation3d ww.value 1 1 1 1 1 1 1 1 1) (mk_position3d ww.value 1 1 1)|)|.value.timestamp) 
					= mk_time wt.value 10 := begin
						simp only [timestamped_pose3d_expr.value],
						dunfold static_timestamped_pose3d_eval,
						simp only [time_expr.value],
						simp only [default_time_env, default_duration_env],
						unfold time_has_lit.cast,
						simp *,
					end,
				rw h0,
				simp only [scalar_expr.value],
				dunfold static_scalar_eval,
				dunfold time.coord,
				let h0 : ((mk_time wt.value 10).to_point.coords 0).coord = 10 := rfl,
				rw h0,
				split,
				repeat { linarith },
			end,
			fails := begin linarith end
		}
		
def target_pose_in_baselink 
	: (constrained (timestamped_pose3d_expr wt bl) (time range |1| to |100|))--(timestamped_pose3d_expr.range_constraint 1 100))
		:= 
		{
			val := |(|mk_time _ 2|),(|mk_pose3d bl.value
			(mk_orientation3d _ 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000 1.000000)
			(mk_position3d _ 1.000000 1.000000 1.000000)|)|,
			holds := begin 
				unfold has_time_range_constraint.to_range_constraint,
				let h0 : (|(|mk_time wt.value 2|),
					(|mk_pose3d bl.value (mk_orientation3d _ 1 1 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1)|)|.value.timestamp) 
					= mk_time wt.value 2 := begin
						simp only [timestamped_pose3d_expr.value],
						dunfold static_timestamped_pose3d_eval,
						simp only [time_expr.value],
						simp only [default_time_env, default_duration_env],
						unfold time_has_lit.cast,
						simp *,
					end,
				rw h0,
				simp only [scalar_expr.value],
				dunfold static_scalar_eval,
				dunfold time.coord,
				let h0 : ((mk_time wt.value 2).to_point.coords 0).coord = 2 := rfl,
				rw h0,
				split,
				repeat { linarith },
			end,
			fails := begin linarith end
		}
	
def target_to_planning_frame : timestamped_geom3d_transform_expr wt ww bl 
	:= ((|wtobl.value.latest|:_))

def target_pose_in_base_link1
	: (constrained (timestamped_pose3d_expr wt bl) (time range |1| to |100|))
		:=
			{
				val := |(|target_to_planning_frame.value.timestamp|),
					(|(target_to_planning_frame.value.value⬝target_pose_in_world.val.value.value)|)|,
				holds := begin
					refl
				end,
				fails := begin
					unfold has_time_range_constraint.to_range_constraint,
					dunfold timestamped_geom3d_transform_expr.value,
					simp only [default_timestamped_pose3d_env, timestamped_pose3d_expr.value, not_and, not_lt, scalar_expr.value,
  					default_timestamped_geom3d_transform_env, static_scalar_eval],
					dunfold static_timestamped_pose3d_eval,
					simp only [default_time_env, gt_iff_lt, default_duration_env, time_expr.value],
					--assume a,
					--squeeze_simp,
					simp only [time_has_lit.cast] at *,

					let h0 : ((|wtobl.value.latest|:_)) = target_to_planning_frame := rfl,
					rw h0.symm,
					let h1 : (discrete_series.latest wtobl.value) = 
						⟨(mk_time wt.value 0.000000),(ww.value.mk_geom3d_transform_to bl.value)⟩ := 
						begin
							dsimp [discrete_series.latest],
							dsimp [wtobl],
							simp only [geom3d_transform_series_has_lit.cast],
						end,
					rw h1,
					simp only [timestamped_geom3d_transform_has_lit.cast],
					dunfold static_timestamped_geom3d_transform_eval,
					simp only [timestamped.timestamp],
					simp only [static_time_eval],
					assume false_,
					let h2 : (mk_time wt.value 0).coord = 0 := rfl,
					rw h2 at false_,
					--let h2 : (false_ → false) := begin
					let h3 : ¬(1 : scalar) < (0 : scalar) := by linarith,
					contradiction,
				end
			}
def timespan : duration_expr wt := ((|mk_duration wt.value 1.000000|:duration_expr wt))
def hasRecentTargetPose : bool_expr := 
		((
			{
				val:=((|mk_time wt.value 0.000000|:time_expr wt))-ᵥ((|target_pose_in_base_link1.val.value.timestamp| : _)),
				holds:=sorry, --THIS CANNOT BE PROVEN.
				fails:=sorry --THIS CAN BE PROVEN.
			}
				:constrained (duration_expr wt) (norm<|timespan.value.coord|)
		)).val <((timespan : duration_expr wt))





end peirce_output